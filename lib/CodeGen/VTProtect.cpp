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
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_os_ostream.h"


using namespace llvm;

namespace llvm {

} // namespace llvm

namespace {
  class VTProtect : public ModulePass {

  private:
    typedef std::map<llvm::Type*, llvm::Constant*> TableMapping;
    TableMapping VTables;

    typedef std::map<llvm::GlobalVariable*, unsigned> TablePosition;
    TablePosition Indexes;

    typedef std::map<llvm::Type*, std::vector<llvm::Type*> > AdjacencyList;
    AdjacencyList Hierarchy;

    void inOrderTraversal(std::vector<llvm::Constant*>& initializers, std::vector<llvm::Type*>& types, llvm::Type* Root,
                          unsigned MaxLen, DataLayout &DL, LLVMContext& context){

        llvm::GlobalVariable* Table = dyn_cast_or_null<GlobalVariable>(VTables[Root]);
        if(Table){
        llvm::Type* RealType = dyn_cast<PointerType>(Table->getType())->getElementType();

        // TODO: Find out what do to with table that have no initializer
        //

        if(Table->hasInitializer()){
          Indexes[Table] = types.size();
          initializers.push_back(Table->getInitializer());
          types.push_back(RealType);

          unsigned RealSize = DL.getTypeSizeInBits(RealType);
          for (unsigned i = 0; i < (MaxLen-RealSize)/8; ++i){
            llvm::Type* Char = llvm::Type::getInt8Ty(context);
            initializers.push_back(llvm::Constant::getNullValue(Char));
            types.push_back(Char);
          }
        }
        }else{
          for (unsigned i = 0; i < MaxLen/8; ++i){
            llvm::Type* Char = llvm::Type::getInt8Ty(context);
            initializers.push_back(llvm::Constant::getNullValue(Char));
            types.push_back(Char);
          }

        }

        AdjacencyList::const_iterator Childrens = Hierarchy.find(Root);
        if(Childrens != Hierarchy.end()){
            for(const auto& Child: Childrens->second){
                inOrderTraversal(initializers, types, Child, MaxLen, DL, context);
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
      IRBuilder<true, llvm::ConstantFolder> IR(M.getContext());

      llvm::NamedMDNode* HierarchyMetadata = M.getNamedMetadata("cps.hierarchy");
      llvm::NamedMDNode* VTablesMetadata = M.getNamedMetadata("cps.vtables");
      // TODO: Change this to handle forests (aka. multiple roots)
      llvm::Type* Root = nullptr;
      unsigned MaxLen = 0;


      /* Tranform hierarchy tree to have it in a nicer format */
      for(llvm::MDNode* op : HierarchyMetadata->operands()){
          assert(op->getNumOperands() == 2);
          llvm::Value* Child = op->getOperand(0);
          llvm::Value* Parent = op->getOperand(1);

          if(Root == nullptr || Child->getType() == Root){
              Root = Parent->getType();
          }

          Hierarchy[Parent->getType()].push_back(Child->getType());
      }


      for(llvm::MDNode* op : VTablesMetadata->operands()){
          assert(op->getNumOperands() == 2);
          llvm::Value* Class = op->getOperand(0);
          llvm::Constant* Table = dyn_cast<Constant>(op->getOperand(1));

          VTables[Class->getType()] = Table;

          //unsigned Size = DL.getPointerTypeSize(Table->getType());
          unsigned Size = DL.getTypeSizeInBits(dyn_cast<PointerType>(Table->getType())->getElementType());
          if(Size > MaxLen){
              MaxLen = Size;
          }
      }

      // Align the length of the largest vtable to closest power of 2
      MaxLen = 1 << ((int) ceil(log(MaxLen)/log(2)));

      std::vector<llvm::Constant*> Initializers;
      std::vector<llvm::Type*> Types;

      inOrderTraversal(Initializers, Types, Root, MaxLen, DL, M.getContext());

      if(Types.empty()){
          return false;
      }

      llvm::StructType* GlobalVTTy = llvm::StructType::create(Types);
      llvm::Constant* GlobalVTInit = llvm::ConstantStruct::get(GlobalVTTy, Initializers);

      llvm::Constant* GlobalVT = M.getOrInsertGlobal("SuperTable", GlobalVTTy);
      dyn_cast<llvm::GlobalVariable>(GlobalVT)->setInitializer(GlobalVTInit);

      for(auto& TblIndex : Indexes){
          llvm::GlobalVariable *Table = TblIndex.first;
          llvm::Value* newTablePtr = IR.CreateConstGEP2_32(GlobalVT,0, TblIndex.second);
          Table->replaceAllUsesWith(newTablePtr);
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
