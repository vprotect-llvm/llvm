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
#include <set>
#include <algorithm>
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_os_ostream.h"


using namespace llvm;

namespace llvm {

} // namespace llvm

namespace {
  class VTProtect : public ModulePass {

  private:

    typedef std::set<llvm::Type*> TypeSet;
    typedef std::pair<unsigned, unsigned> Range;

    struct RangeCompare
    {
        //overlapping ranges are considered equivalent
        bool operator()(const Range& lhv, const Range& rhv) const
        {
            return lhv.second < rhv.first;
        }
    };

    // Represents a type with all the information about it's position in the type hierarchy
    typedef struct {
       llvm::Type* Typ;
       llvm::GlobalVariable* VTable; //The VTable associated with this type
       TypeSet Children;
       TypeSet Parents;

       // To Separate Connected components
       //llvm::Type* Representative;

       // In spanning tree
       llvm::Type* ChosenParent;
       TypeSet Preds;


       unsigned Label; //Label in the hierarchy
       std::set<Range, RangeCompare> SubtypeRanges;

       unsigned Index; // Index in the global Table

       // TODO : set if class can appear in a multiple inheritence scheme where it is not the first parent as the vtable pointer will not be aligned with normal vtables
       bool PossibleMultiInheritance = false;
    } TypeNode;


    typedef std::map<llvm::Type*, std::set<llvm::Type*> > AdjList;
    AdjList m_ParentRelation;

    typedef std::map<llvm::Type*, TypeNode> Hierarchy;
    Hierarchy m_Hierarchy;

    typedef std::vector<llvm::Type*> TypeSeq;
    TypeSeq TopologicalOrdering;

    std::map<unsigned, llvm::Type*> Labels;

    /* Set of all the roots in the hierarchy forest */
    TypeSet m_Roots;

    /* Total number of bigger tables we build, one for each root */
    unsigned NumTables = 0;


    void CollectHierarchyMetadata(llvm::Module &M, llvm::StringRef Name){
      llvm::NamedMDNode* HierarchyMetadata = M.getNamedMetadata(Name);

      /* Tranform hierarchy tree to have it in a nicer format */
      for(llvm::MDNode* op : HierarchyMetadata->operands()){
        assert(op->getNumOperands() == 2);
        llvm::Type* Child = op->getOperand(0)->getType();
        llvm::Type* Parent = op->getOperand(1)->getType();

        m_Hierarchy[Parent].Children.insert(Child);
        m_Hierarchy[Child].Parents.insert(Parent);
        m_ParentRelation[Child].insert(Parent);

        // set multiple inheritance bit
        if(m_Hierarchy[Child].Parents.size() > 1){
          std::set<llvm::Type*> PotentialMultiClasses;
          PotentialMultiClasses.insert(Parent);
          while(PotentialMultiClasses.size() > 0){
            llvm::Type* Cur = *PotentialMultiClasses.begin();
            PotentialMultiClasses.erase(Cur);
            m_Hierarchy[Cur].PossibleMultiInheritance = true;
            for(llvm::Type* MultiParent : m_Hierarchy[Cur].Parents){
              PotentialMultiClasses.insert(MultiParent);
            }
          }
        }
      }
    }

    /* Returns the size of the largest vTable */
    unsigned CollectVTablesMetadata(llvm::Module &M, llvm::StringRef Name, DataLayout &DL){
      llvm::NamedMDNode* VTablesMetadata = M.getNamedMetadata(Name);

      unsigned MaxLen = 0;
      for(llvm::MDNode* op : VTablesMetadata->operands()){
        assert(op->getNumOperands() == 2);
        llvm::Type* Typ = op->getOperand(0)->getType();
        llvm::GlobalVariable* Table = dyn_cast_or_null<GlobalVariable>(op->getOperand(1));
        
        if(Table == nullptr){
            continue;
        }

        m_Hierarchy[Typ].Typ = Typ;
        m_Hierarchy[Typ].VTable = Table;

        unsigned Size = DL.getTypeSizeInBits(dyn_cast<PointerType>(Table->getType())->getElementType());
        if(Size > MaxLen){
          MaxLen = Size;
        }
      }

      return MaxLen;
    }

    void TopologicalSort(){
        TypeSet Roots;


        for(auto const& Typ: m_Hierarchy){
          if(Typ.second.Parents.empty()){
            Roots.insert(Typ.first);
            m_Roots.insert(Typ.first);
          }
        }

        while(!Roots.empty()){
          llvm::Type* Next = *Roots.begin();
          Roots.erase(Next);
          TopologicalOrdering.push_back(Next);

          for(llvm::Type* Child : m_Hierarchy[Next].Children){
            m_ParentRelation[Child].erase(Next);
            if(m_ParentRelation[Child].empty()){
                Roots.insert(Child);
            }
          }
        }

        assert(TopologicalOrdering.size() == m_Hierarchy.size());
    }

    void BuildSpanningForest(){
      // Algo as in p253-agrawal
      for(llvm::Type* Typ: TopologicalOrdering){
        if(!m_Hierarchy[Typ].Parents.empty()){
          unsigned MaxPredSize = 0;
          llvm::Type* BestParent = nullptr;
          for(llvm::Type* Parent : m_Hierarchy[Typ].Parents){
            if(m_Hierarchy[Parent].Preds.size() > MaxPredSize){
              MaxPredSize = m_Hierarchy[Parent].Preds.size();
              BestParent = Parent;
            }
          }

          m_Hierarchy[Typ].ChosenParent = BestParent;
          m_Hierarchy[Typ].Preds = m_Hierarchy[BestParent].Preds;
          m_Hierarchy[Typ].Preds.insert(BestParent);
        } else {
          m_Hierarchy[Typ].Preds.insert(nullptr);
        }
      }
    }

    void CollectInitializers(std::vector<llvm::Constant*>& initializers, std::vector<llvm::Type*>& types, llvm::Type* CurNode,
                          unsigned MaxLen, DataLayout &DL, LLVMContext& context, unsigned& CurLabel){

      llvm::GlobalVariable* Table = m_Hierarchy[CurNode].VTable;
      

        unsigned RealSize = 0;
        Labels[CurLabel] = CurNode;
        m_Hierarchy[CurNode].Label = CurLabel;
        ++CurLabel;

        m_Hierarchy[CurNode].Index = types.size();

        if(Table){ // TODO: not sure when this happens, happened when launching
          // check-all on llvm build
          llvm::Type* RealType = dyn_cast<PointerType>(Table->getType())->getElementType();
          RealSize = DL.getTypeSizeInBits(RealType);
          types.push_back(RealType);

          if(Table->hasInitializer()){
            initializers.push_back(Table->getInitializer());
          } else {
            initializers.push_back(llvm::UndefValue::get(RealType));
          }
        }

        // Padding
        llvm::Type* Byte = llvm::Type::getInt8Ty(context);
        unsigned PaddingSize = MaxLen - RealSize;
        assert(PaddingSize % 8 == 0);
        llvm::Type* ArrayTy = llvm::ArrayType::get(Byte, PaddingSize/8);
        types.push_back(ArrayTy);
        initializers.push_back(llvm::UndefValue::get(ArrayTy));

        for(llvm::Type* Child : m_Hierarchy[CurNode].Children){
          if(m_Hierarchy[Child].ChosenParent == CurNode){
            CollectInitializers(initializers, types, Child, MaxLen, DL, context, CurLabel);
          }
      }
    }


    llvm::GlobalVariable* CreateGlobalTable(llvm::Module &M, std::vector<llvm::Constant*> Initializers, std::vector<llvm::Type*> Types, unsigned MaxTableLen){
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

    void CollectRanges(llvm::Type* CurType){
        TypeNode* CurNode = &m_Hierarchy[CurType];
        unsigned CurLabel = CurNode->Label;
        if(CurNode->SubtypeRanges.find(Range(CurLabel, CurLabel)) != CurNode->SubtypeRanges.end()){
            //Already collected ranges
            return;
        }

        for(llvm::Type* Child : CurNode->Children){
            CollectRanges(Child);
            for(Range const& range: m_Hierarchy[Child].SubtypeRanges){
              auto const& iter = CurNode->SubtypeRanges.find(range);
              if(iter == CurNode->SubtypeRanges.end()){
                CurNode->SubtypeRanges.insert(range);
              }else{
                Range merged = Range(std::min(range.first, iter->first), std::max(range.second, iter->second));
                CurNode->SubtypeRanges.erase(iter);
                CurNode->SubtypeRanges.insert(merged);
              }
            }
        }

        CurNode->SubtypeRanges.insert(Range(CurLabel, CurLabel));

        // Merge
        std::set<Range, RangeCompare> Merged;
        Range current = *CurNode->SubtypeRanges.begin();

        for(Range const& range: CurNode->SubtypeRanges){
          if(range.first <= (current.second + 1)){
            current.second = range.second;
          } else {
            Merged.insert(current);
            current = range;
          }
        }

        Merged.insert(current);

        CurNode->SubtypeRanges = Merged;

    }

     llvm::BasicBlock* EmitBoundCheck(IRBuilder<true, llvm::ConstantFolder> &IRB, llvm::BasicBlock* ExitBB, llvm::Value* Low, llvm::Value* High){

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

      return PredBB;
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

      CollectHierarchyMetadata(M, "cps.hierarchy");
      unsigned MaxTableLen = CollectVTablesMetadata(M, "cps.vtables", DL);
    
      // Lost information about tables (TODO: not sure what this means)
      if(MaxTableLen == 0){
        return false;
      }

      // Exit if there is nothing to do
      if(m_Hierarchy.empty()){
        return false;
      }

      // Align the length of the largest vtable to closest power of 2
      MaxTableLen = 1 << ((int) ceil(log(MaxTableLen)/log(2)));
      // Change for optimization here since you can use different length for different connected componenents TODO

      TopologicalSort();
      BuildSpanningForest();

      std::vector<llvm::Constant*> Initializers;
      std::vector<llvm::Type*> Types;
      unsigned Label = 0;

      for(llvm::Type* Root : m_Roots){
        CollectInitializers(Initializers, Types, Root, MaxTableLen, DL, M.getContext(), Label);
      }


      for(llvm::Type* Root: m_Roots){
        CollectRanges(Root);
      }

      llvm::GlobalVariable* GlobalVT = CreateGlobalTable(M, Initializers, Types, MaxTableLen);

      for(auto const& Node: m_Hierarchy){
        llvm::GlobalVariable *Table = Node.second.VTable;

        //TODO: Check why table is sometimes null here
        if(Table && Table->getNumUses()){
          llvm::Value* newTablePtr = IRB.CreateConstGEP2_32(GlobalVT, 0, Node.second.Index);
          Table->replaceAllUsesWith(newTablePtr);
        }
      }


      //***************************************** Checks ******************************************//
      for(llvm::Function& fun: M.getFunctionList()){
        if(fun.isIntrinsic()) continue; // Not too sure about this
        /* DEBUG : */
//        llvm::Value* PrintPtr = M.getOrInsertFunction("_Z8printptrPv", llvm::Type::getVoidTy(M.getContext()), IntegerType::getInt8PtrTy(M.getContext()), nullptr);
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

            /* TODO : UGLY, fix this by factorizing code emission in separate function to be able to handle index chek for memptrs */
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
                  TypeNode* Node = &m_Hierarchy[Typ];

                  IRB.SetInsertPoint(&block, vptr);
                  
                  // Go backwards for Desctructor and Typeinfo
                  llvm::Value* TblPtr = IRB.CreateConstGEP1_64(&inst, offset, "real.vtable"); 

                  if(!Node->PossibleMultiInheritance){
                    EmitAlignmentCheck(IRB, DL, M.getContext(), ExitBB, TblPtr, MaxTableLen);
                  }

                  std::set<llvm::BasicBlock*> PredecessorBlocks;
                  std::set<llvm::BasicBlock*> PreviousBlocks;

                  for(Range const& range : Node->SubtypeRanges){

                    llvm::Type* LowTyp = Labels[range.first];
                    llvm::Type* HighTyp = Labels[range.second];

                   // llvm::errs() << "Inserting checks for (Label = " << Node->Label << ", Index = " << Node->Index << ") : ";
                   // Typ->dump();
                   // llvm::errs() << "Possible subtypes : \n";
                   // for(unsigned i = range.first; i <= range.second; ++i){
                   //   llvm::errs() << " - (Label = " << i << ", Index = " << m_Hierarchy[Labels[i]].Index << ") ";
                   //   Labels[i]->dump();
                   // }

                    llvm::Value* BasePtr = IRB.CreateConstGEP2_32(GlobalVT, 0, m_Hierarchy[LowTyp].Index);
                    llvm::Value* EndPtr = IRB.CreateConstGEP2_32(GlobalVT, 0, std::min(m_Hierarchy[HighTyp].Index + 1, (unsigned) (Types.size() - 1))); // TODO : +1 is to account for multiple inheritance shift

                    /* DEBUG :*/
                   // IRB.CreateCall(PrintPtr, IRB.CreateBitCast(BasePtr, IntegerType::getInt8PtrTy(M.getContext())));
                   // IRB.CreateCall(PrintPtr, IRB.CreateBitCast(TblPtr, IntegerType::getInt8PtrTy(M.getContext())));
                   // IRB.CreateCall(PrintPtr, IRB.CreateBitCast(EndPtr, IntegerType::getInt8PtrTy(M.getContext())));
                    /* END DEBUG*/

                    llvm::BasicBlock* LowCheck = EmitBoundCheck(IRB, ExitBB, IRB.CreateBitCast(BasePtr, TblPtr->getType()), TblPtr);
                    llvm::BasicBlock* HighCheck = EmitBoundCheck(IRB, ExitBB, TblPtr, IRB.CreateBitCast(EndPtr, TblPtr->getType()));

                    // Update false branch
                    for(llvm::BasicBlock* PredBB: PredecessorBlocks){
                      llvm::BranchInst* Terminator = dyn_cast<llvm::BranchInst>(PredBB->getTerminator());
                      Terminator->setSuccessor(1, LowCheck);
                    }

                    // Update true branch
                    for(llvm::BasicBlock* PreviousBB: PreviousBlocks){
                      llvm::BranchInst* Terminator = dyn_cast<llvm::BranchInst>(PreviousBB->getTerminator());
                      Terminator->setSuccessor(0, IRB.GetInsertBlock());
                    }

                    PredecessorBlocks.clear();
                    PredecessorBlocks.insert(LowCheck);
                    PredecessorBlocks.insert(HighCheck);
                    PreviousBlocks.insert(HighCheck);
                  }
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
