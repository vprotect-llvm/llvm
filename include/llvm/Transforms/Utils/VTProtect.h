//===--- llvm/CodeGen/VTProtect.cpp - Virtual Table Protection --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_CPIVTPROTECT_H
#define LLVM_CODEGEN_CPIVTPROTECT_H

#include <llvm/Pass.h>

namespace llvm {

/// createVTProtectPass - This pass enforces the layout of the virtual tables in
/// memory
Pass *createVTProtectPass();

} // namespace llvm

#endif // LLVM_CODEGEN_CPIVTPROTECT_H
