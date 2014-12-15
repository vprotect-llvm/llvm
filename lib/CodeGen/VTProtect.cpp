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

    bool doPassInitialization(Module &M);
    bool doPassFinalization(Module &M);
    bool runOnFunction(Function &F);

  public:
    static char ID; // Pass identification, replacement for typeid.
    VTProtect(): ModulePass(ID) {
    }

    virtual bool runOnModule(Module &M) {
      errs() << "[VTProtect] Module: "
                   << M.getModuleIdentifier() << "\n";

      // Add module-level code (e.g., runtime support function prototypes)
//      doPassInitialization(M);


      // Finalization (mostly for statistics)
//      doPassFinalization(M);
      return true;
    }


  };

} // end anonymous namespace

char VTProtect::ID = 0;
static RegisterPass<VTProtect>X("vt-protect", "Virtual Table protection pass", false, false);

Pass *llvm::createVTProtectPass() {
  return new VTProtect();
}
