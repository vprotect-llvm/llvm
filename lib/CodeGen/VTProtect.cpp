//===-- VTProtect.cpp - Virtual Table Protection ------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "vt-protect"
#include "llvm/CodeGen/VTProtect.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_os_ostream.h"


using namespace llvm;

namespace llvm {

} // namespace llvm

namespace {
  class VTProtect : public ModulePass {

  private:
    typedef std::map<llvm::Type*, llvm::GlobalVariable*> TableMapping;
    /* Mapping between each class and its VirtualTable */
    TableMapping VTables;

    typedef std::map<llvm::GlobalVariable*, unsigned> TablePosition;
    /* Keeps track of the position of each old VTable in their corresponding new global one */
    TablePosition Indexes;

    typedef std::map<llvm::Type*, std::vector<llvm::Type*> > AdjacencyList;
    /* Map from parents to their list of childs */
    AdjacencyList Hierarchy;

    typedef std::map<llvm::Type*, llvm::Type*> RootMap;
    /* Map from every node in the type tree to it's root */
    RootMap ChildToRoots;

    /* Map of each Root to it's corresponding new global table */
    TableMapping RootTables;

    typedef llvm::SmallPtrSet<llvm::Type*, 100> TypeSet;
    /* Set of all the roots in the hierarchy forest */
    TypeSet Roots;

    /* Total number of bigger tables we build, one for each root */
    unsigned NumTables = 0;


    llvm::GlobalVariable* createGlobalTable(llvm::Module &M, std::vector<llvm::Constant*> Initializers, std::vector<llvm::Type*> Types, unsigned MaxTableLen){
        // Use unique name
        char Name[128];
        char Type[128];
        ::sprintf(Type, "SuperTable%dType", NumTables);
        ::sprintf(Name, "SuperTable%d", NumTables++);

        llvm::StructType* GlobalVTTy = llvm::StructType::create(Types, Type);
        llvm::Constant* GlobalVTInit = llvm::ConstantStruct::get(GlobalVTTy, Initializers);

        llvm::GlobalVariable* GlobalVT = dyn_cast<llvm::GlobalVariable>(M.getOrInsertGlobal(Name, GlobalVTTy));
        GlobalVT->setInitializer(GlobalVTInit);
        GlobalVT->setAlignment(MaxTableLen);

        return GlobalVT;
    }


    void collectHierarchyMetadata(llvm::Module &M, llvm::StringRef Name){
      llvm::NamedMDNode* HierarchyMetadata = M.getNamedMetadata(Name);

      /* Tranform hierarchy tree to have it in a nicer format */
      for(llvm::MDNode* op : HierarchyMetadata->operands()){
        assert(op->getNumOperands() == 2);
        llvm::Type* Child = op->getOperand(0)->getType();
        llvm::Type* Parent = op->getOperand(1)->getType();

        Hierarchy[Parent].push_back(Child);

        while(ChildToRoots.find(Parent) != ChildToRoots.end()){
          Parent = ChildToRoots[Parent];
        }

        for(auto& OldRootChild : ChildToRoots){
          if(OldRootChild.second == Child){
            OldRootChild.second = Parent;
          }
        }

        ChildToRoots[Child] = Parent;

      }

      for(auto& ChildRoot : ChildToRoots){
        Roots.insert(ChildRoot.second);
      }

    }


    /* Returns the size of the largest vTable */
    unsigned collectVTablesMetadata(llvm::Module &M, llvm::StringRef Name, DataLayout &DL){
      llvm::NamedMDNode* VTablesMetadata = M.getNamedMetadata(Name);

      unsigned MaxLen = 0;
      for(llvm::MDNode* op : VTablesMetadata->operands()){
        assert(op->getNumOperands() == 2);
        llvm::Type* Typ = op->getOperand(0)->getType();
        llvm::GlobalVariable* Table = dyn_cast<GlobalVariable>(op->getOperand(1));

        VTables[Typ] = Table;
        if(ChildToRoots.find(Typ) == ChildToRoots.end()){
          ChildToRoots[Typ] = Typ;
          Roots.insert(Typ);
        }

        unsigned Size = DL.getTypeSizeInBits(dyn_cast<PointerType>(Table->getType())->getElementType());
        if(Size > MaxLen){
          MaxLen = Size;
        }
      }

      return MaxLen;
    }


    llvm::Type* getRightMostChild(llvm::Type* parent){
        AdjacencyList::const_iterator Childrens = Hierarchy.find(parent);
        if(Childrens == Hierarchy.end() || Childrens->second.empty()){
            return parent;
        } else {
           return getRightMostChild(Childrens->second.back());
        }
    }


    void collectInitializers(std::vector<llvm::Constant*>& initializers, std::vector<llvm::Type*>& types, llvm::Type* Root,
                          unsigned MaxLen, DataLayout &DL, LLVMContext& context){

      llvm::GlobalVariable* Table = dyn_cast_or_null<GlobalVariable>(VTables[Root]);
      unsigned RealSize = 0;

      if(Table){ //Not sure if table should always be defined
        llvm::Type* RealType = dyn_cast<PointerType>(Table->getType())->getElementType();
        RealSize = DL.getTypeSizeInBits(RealType);

        if(Table->hasInitializer()){
          Indexes[Table] = types.size();
          // TODO: Find out what do to with table that have no initializer
          initializers.push_back(Table->getInitializer());
          types.push_back(RealType);
        } else {
           RealSize = 0;
        }
      }

      // Padding
      llvm::Type* Byte = llvm::Type::getInt8Ty(context);
      unsigned PaddingSize = MaxLen - RealSize;
      assert(PaddingSize % 8 == 0);
      llvm::Type* ArrayTy = llvm::ArrayType::get(Byte, PaddingSize/8);
      types.push_back(ArrayTy);
      initializers.push_back(llvm::Constant::getNullValue(ArrayTy));

      // Run on childrens
      AdjacencyList::const_iterator Childrens = Hierarchy.find(Root);
      if(Childrens != Hierarchy.end()){
        for(const auto& Child: Childrens->second){
          collectInitializers(initializers, types, Child, MaxLen, DL, context);
        }
      }
    }


    void EmitBoundCheck(IRBuilder<true, llvm::ConstantFolder> &IRB, llvm::BasicBlock* ExitBB, llvm::Value* Low, llvm::Value* High){

      llvm::Value* Cond = IRB.CreateICmpULE(Low, High);

      Instruction *InsertPt = IRB.GetInsertPoint();
      assert(InsertPt);

      BasicBlock *PredBB = InsertPt->getParent();
      BasicBlock *NextBB = PredBB->splitBasicBlock(InsertPt, "boundcheck.end");

      IRB.SetInsertPoint(PredBB, &PredBB->back());
      IRB.CreateCondBr(Cond, NextBB, ExitBB);
      PredBB->back().eraseFromParent();

      assert(InsertPt == NextBB->begin());
      IRB.SetInsertPoint(NextBB, NextBB->begin());

    }

    void EmitAlignmentCheck(IRBuilder<true, llvm::ConstantFolder> &IRB, llvm::DataLayout &DL,llvm::LLVMContext &Context,
                            llvm::BasicBlock* ExitBB, llvm::Value* Pointer, unsigned Alignment){

      llvm::IntegerType* IntTy = Type::getIntNTy(Context, DL.getPointerSizeInBits());

      llvm::Value* PtrInt = IRB.CreatePtrToInt(Pointer, IntTy);
      llvm::Value* Mask = IRB.getInt(APInt(DL.getPointerSizeInBits(), Alignment/8 - 1));

      llvm::Value* LowerBits = IRB.CreateAnd(PtrInt, Mask);
      llvm::Value* Cond = IRB.CreateIsNull(LowerBits);

      Instruction *InsertPt = IRB.GetInsertPoint();
      assert(InsertPt);

      BasicBlock *PredBB = InsertPt->getParent();
      BasicBlock *NextBB = PredBB->splitBasicBlock(InsertPt, "aligncheck.end");

      IRB.SetInsertPoint(PredBB, &PredBB->back());
      IRB.CreateCondBr(Cond, NextBB, ExitBB);
      PredBB->back().eraseFromParent();

      assert(InsertPt == NextBB->begin());
      IRB.SetInsertPoint(NextBB, NextBB->begin());
    }

  public:
    static char ID; // Pass identification, replacement for typeid.
    VTProtect(): ModulePass(ID) {
    }

    virtual bool runOnModule(Module &M) {
      //errs() << "[VTProtect] Module: "
      //             << M.getModuleIdentifier() << "\n";

      DataLayout DL(&M);
      IRBuilder<true, llvm::ConstantFolder> IRB(M.getContext());

      collectHierarchyMetadata(M, "cps.hierarchy");
      unsigned MaxTableLen = collectVTablesMetadata(M, "cps.vtables", DL);

      // Align the length of the largest vtable to closest power of 2
      MaxTableLen = 1 << ((int) ceil(log(MaxTableLen)/log(2)));


      for(llvm::Type* Root : Roots){
        std::vector<llvm::Constant*> Initializers;
        std::vector<llvm::Type*> Types;

        collectInitializers(Initializers, Types, Root, MaxTableLen, DL, M.getContext());

        if(Types.empty()){
          continue; // Can this really happen ?
        }

        llvm::GlobalVariable* GlobalVT = createGlobalTable(M, Initializers, Types, MaxTableLen);
        RootTables[Root] = GlobalVT;

        for(auto& ChildRoot: ChildToRoots){
          if(ChildRoot.second == Root){
            llvm::GlobalVariable *Table = VTables[ChildRoot.first];
            //Check why table is sometimes null here
            if(Table && Table->getNumUses()){
                llvm::Value* newTablePtr = IRB.CreateConstGEP2_32(GlobalVT, 0, Indexes[Table]);
                Table->replaceAllUsesWith(newTablePtr);
            }
          }
        }
      }


      for(llvm::Function& fun: M.getFunctionList()){
        if(fun.isIntrinsic()) continue; // Not too sure about this
        /* DEBUG : */
        llvm::Value* PrintPtr = M.getOrInsertFunction("_Z8printptrPv", llvm::Type::getVoidTy(M.getContext()), IntegerType::getInt8PtrTy(M.getContext()), nullptr);
        /* END DEBUG */
        llvm::Value* Abort = M.getOrInsertFunction("abort", llvm::Type::getVoidTy(M.getContext()), nullptr);
        llvm::BasicBlock* ExitBB = BasicBlock::Create(M.getContext(), "exit", &fun);

        ExitBB->getInstList().push_back(CallInst::Create(Abort));
        llvm::Instruction* Terminator;
        if(fun.getReturnType()->isVoidTy()){
          Terminator = ReturnInst::Create(M.getContext());
        }else{
          Terminator = ReturnInst::Create(M.getContext(), llvm::UndefValue::get(fun.getReturnType()));
        }
        ExitBB->getInstList().push_back(Terminator);

        for(llvm::BasicBlock& block : fun.getBasicBlockList()){
          for(llvm::Instruction& inst : block.getInstList()){
            /* HACK : UGLY, fix this by factorizing code emission in separate function to be able to handle index chek for memptrs */
            llvm::MDNode* metadata = inst.getMetadata("cps.vfn");
            int offset;
            if(metadata){
                offset = -2;
            } else {
                //IGNORE OTHER METADATA FOR NOW
                //metadata = inst.getMetadata("cps.memptr");
                offset = 0;
            }

            if(metadata){
              for(llvm::Value* user : inst.users()){
                llvm::Instruction* vptr;
                if((vptr = dyn_cast<llvm::Instruction>(user))){

                  llvm::Type* Typ = metadata->getOperand(0)->getType();
                  llvm::Type* End = getRightMostChild(Typ);
                  llvm::GlobalVariable* GlobalVT = RootTables[ChildToRoots[Typ]];

                  IRB.SetInsertPoint(&block, vptr);
                  llvm::Value* BasePtr = IRB.CreateConstGEP2_32(GlobalVT, 0, Indexes[VTables[Typ]]);
                  llvm::Value* EndPtr = IRB.CreateConstGEP2_32(GlobalVT, 0, Indexes[VTables[End]]);
                  llvm::Value* TblPtr = IRB.CreateConstGEP1_64(vptr->getOperand(0), offset); // Go backwards for Desctructor and Typeinfo

                  /* DEBUG :*/
                  IRB.CreateCall(PrintPtr, IRB.CreateBitCast(BasePtr, IntegerType::getInt8PtrTy(M.getContext())));
                  IRB.CreateCall(PrintPtr, IRB.CreateBitCast(EndPtr, IntegerType::getInt8PtrTy(M.getContext())));
                  IRB.CreateCall(PrintPtr, IRB.CreateBitCast(TblPtr, IntegerType::getInt8PtrTy(M.getContext())));
                  /* END DEBUG*/

                  EmitBoundCheck(IRB, ExitBB, TblPtr, IRB.CreateBitCast(EndPtr, TblPtr->getType()));
                  EmitBoundCheck(IRB, ExitBB, IRB.CreateBitCast(BasePtr, TblPtr->getType()), TblPtr);
                  EmitAlignmentCheck(IRB, DL, M.getContext(), ExitBB, TblPtr, MaxTableLen);

                }
              }
            }
          }
        }

        if(ExitBB->getNumUses() == 0) {
          ExitBB->eraseFromParent();
        }

      }

      return true;
    }


  };

} // end anonymous namespace

char VTProtect::ID = 0;
static RegisterPass<VTProtect>X("vt-protect", "Virtual Table protection pass", false, false);

Pass *llvm::createVTProtectPass() {
  return new VTProtect();
}
