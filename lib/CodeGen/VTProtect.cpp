//===-- VTProtect.cpp - Virtual Table Protection ------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass splits the stack into the safe stack (kept as-is for LLVM backend)
// and the unsafe stack (explicitly allocated and managed through the runtime
// support library).
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
    TypeSet Roots;

    unsigned NumTables = 0;

    llvm::GlobalVariable* createGlobalTable(llvm::Module &M, std::vector<llvm::Constant*> Initializers, std::vector<llvm::Type*> Types, unsigned MaxTableLen){

        llvm::StructType* GlobalVTTy = llvm::StructType::create(Types);
        llvm::Constant* GlobalVTInit = llvm::ConstantStruct::get(GlobalVTTy, Initializers);

        // Use unique name
        char Name[128];
        ::sprintf(Name, "SuperTable%d", NumTables++);
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
        }
      }

      // Padding
      llvm::Type* Char = llvm::Type::getInt8Ty(context);
      unsigned CharSize = DL.getTypeSizeInBits(Char);
      unsigned PaddingSize = MaxLen - RealSize;
      assert(PaddingSize % CharSize == 0);
      llvm::Type* ArrayTy = llvm::ArrayType::get(Char, PaddingSize/CharSize);
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
        llvm::Value* Abort = M.getOrInsertFunction("abort", Type::getVoidTy(M.getContext()), nullptr);
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
            llvm::MDNode* metadata = inst.getMetadata("cps.vload");
            if(metadata){
              // I don't think this is necessarily true
              llvm::Instruction* vptr = inst.getNextNode();

              llvm::Type* Typ = metadata->getOperand(0)->getType();
              llvm::Type* End = getRightMostChild(Typ);
              llvm::GlobalVariable* GlobalVT = RootTables[ChildToRoots[Typ]];

              IRB.SetInsertPoint(&block, vptr);
              llvm::Value* BasePtr = IRB.CreateConstGEP2_32(GlobalVT, 0, Indexes[VTables[Typ]]);
              llvm::Value* EndPtr = IRB.CreateConstGEP2_32(GlobalVT, 0, Indexes[VTables[End]]);
              llvm::Value* TblPtr = IRB.CreateConstGEP1_64(vptr->getOperand(0), -2); // Apparently there is need for fixing the pointer

              llvm::BasicBlock* PrevBB = vptr->getParent();
              llvm::BasicBlock* NextBB = PrevBB->splitBasicBlock(vptr);

              IRB.SetInsertPoint(PrevBB, &PrevBB->back());
              llvm::Value* CmpLowBound = IRB.CreateICmpUGE(TblPtr, IRB.CreateBitCast(BasePtr, TblPtr->getType()));
              IRB.CreateCondBr(CmpLowBound, NextBB, ExitBB);

              llvm::BasicBlock* Next2BB = NextBB->splitBasicBlock(vptr);

              IRB.SetInsertPoint(NextBB, &NextBB->back());
              llvm::Value* CmpHighBound = IRB.CreateICmpULE(TblPtr, IRB.CreateBitCast(EndPtr, TblPtr->getType()));
              IRB.CreateCondBr(CmpHighBound, Next2BB, ExitBB);

              NextBB->back().eraseFromParent();
              PrevBB->back().eraseFromParent();


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
