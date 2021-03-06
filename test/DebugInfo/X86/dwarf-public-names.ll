; RUN: llc -mtriple=x86_64-pc-linux-gnu -filetype=obj -o %t.o < %s
; RUN: llvm-dwarfdump -debug-dump=pubnames %t.o | FileCheck --check-prefix=LINUX %s
; RUN: llc -mtriple=x86_64-apple-darwin12 -filetype=obj -o %t.o < %s
; RUN: llvm-dwarfdump -debug-dump=pubnames %t.o | FileCheck --check-prefix=DARWIN %s
; ModuleID = 'dwarf-public-names.cpp'
;
; Generated from:
;
; struct C {
;   void member_function();
;   static int static_member_function();
;   static int static_member_variable;
; };
;
; int C::static_member_variable = 0;
;
; void C::member_function() {
;   static_member_variable = 0;
; }
;
; int C::static_member_function() {
;   return static_member_variable;
; }
;
; C global_variable;
;
; int global_function() {
;   return -1;
; }
;
; namespace ns {
;   void global_namespace_function() {
;     global_variable.member_function();
;   }
;   int global_namespace_variable = 1;
; }

; Darwin shouldn't be generating the section by default
; DARWIN: debug_pubnames
; DARWIN: {{^$}}

; Skip the output to the header of the pubnames section.
; LINUX: debug_pubnames
; LINUX: unit_size = 0x00000128

; Check for each name in the output.
; LINUX-DAG: "ns"
; LINUX-DAG: "C::static_member_function"
; LINUX-DAG: "global_variable"
; LINUX-DAG: "ns::global_namespace_variable"
; LINUX-DAG: "ns::global_namespace_function"
; LINUX-DAG: "global_function"
; LINUX-DAG: "C::static_member_variable"
; LINUX-DAG: "C::member_function"

%struct.C = type { i8 }

@_ZN1C22static_member_variableE = global i32 0, align 4
@global_variable = global %struct.C zeroinitializer, align 1
@_ZN2ns25global_namespace_variableE = global i32 1, align 4

define void @_ZN1C15member_functionEv(%struct.C* %this) nounwind uwtable align 2 {
entry:
  %this.addr = alloca %struct.C*, align 8
  store %struct.C* %this, %struct.C** %this.addr, align 8
  call void @llvm.dbg.declare(metadata !{%struct.C** %this.addr}, metadata !28, metadata !{metadata !"0x102"}), !dbg !30
  %this1 = load %struct.C** %this.addr
  store i32 0, i32* @_ZN1C22static_member_variableE, align 4, !dbg !31
  ret void, !dbg !32
}

declare void @llvm.dbg.declare(metadata, metadata, metadata) nounwind readnone

define i32 @_ZN1C22static_member_functionEv() nounwind uwtable align 2 {
entry:
  %0 = load i32* @_ZN1C22static_member_variableE, align 4, !dbg !33
  ret i32 %0, !dbg !33
}

define i32 @_Z15global_functionv() nounwind uwtable {
entry:
  ret i32 -1, !dbg !34
}

define void @_ZN2ns25global_namespace_functionEv() nounwind uwtable {
entry:
  call void @_ZN1C15member_functionEv(%struct.C* @global_variable), !dbg !35
  ret void, !dbg !36
}

attributes #0 = { nounwind uwtable }
attributes #1 = { nounwind readnone }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!38}

!0 = metadata !{metadata !"0x11\004\00clang version 3.3 (http://llvm.org/git/clang.git a09cd8103a6a719cb2628cdf0c91682250a17bd2) (http://llvm.org/git/llvm.git 47d03cec0afca0c01ae42b82916d1d731716cd20)\000\00\000\00\000", metadata !37, metadata !1, metadata !1, metadata !2, metadata !24,  metadata !1} ; [ DW_TAG_compile_unit ] [/usr2/kparzysz/s.hex/t/dwarf-public-names.cpp] [DW_LANG_C_plus_plus]
!1 = metadata !{}
!2 = metadata !{metadata !3, metadata !18, metadata !19, metadata !20}
!3 = metadata !{metadata !"0x2e\00member_function\00member_function\00_ZN1C15member_functionEv\009\000\001\000\006\00256\000\009", metadata !4, null, metadata !5, null, void (%struct.C*)* @_ZN1C15member_functionEv, null, metadata !12, metadata !1} ; [ DW_TAG_subprogram ] [line 9] [def] [member_function]
!4 = metadata !{metadata !"0x29", metadata !37} ; [ DW_TAG_file_type ]
!5 = metadata !{metadata !"0x15\00\000\000\000\000\000\000", i32 0, null, null, metadata !6, null, null, null} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!6 = metadata !{null, metadata !7}
!7 = metadata !{metadata !"0xf\00\000\0064\0064\000\001088", i32 0, null, metadata !8} ; [ DW_TAG_pointer_type ] [line 0, size 64, align 64, offset 0] [artificial] [from C]
!8 = metadata !{metadata !"0x13\00C\001\008\008\000\000\000", metadata !37, null, null, metadata !9, null, null, null} ; [ DW_TAG_structure_type ] [C] [line 1, size 8, align 8, offset 0] [def] [from ]
!9 = metadata !{metadata !10, metadata !12, metadata !14}
!10 = metadata !{metadata !"0xd\00static_member_variable\004\000\000\000\004096", metadata !37, metadata !8, metadata !11, null} ; [ DW_TAG_member ] [static_member_variable] [line 4, size 0, align 0, offset 0] [static] [from int]
!11 = metadata !{metadata !"0x24\00int\000\0032\0032\000\000\005", null, null} ; [ DW_TAG_base_type ] [int] [line 0, size 32, align 32, offset 0, enc DW_ATE_signed]
!12 = metadata !{metadata !"0x2e\00member_function\00member_function\00_ZN1C15member_functionEv\002\000\000\000\006\00256\000\002", metadata !4, metadata !8, metadata !5, null, null, null, i32 0, metadata !13} ; [ DW_TAG_subprogram ] [line 2] [member_function]
!13 = metadata !{metadata !"0x24"}                      ; [ DW_TAG_base_type ] [line 0, size 0, align 0, offset 0]
!14 = metadata !{metadata !"0x2e\00static_member_function\00static_member_function\00_ZN1C22static_member_functionEv\003\000\000\000\006\00256\000\003", metadata !4, metadata !8, metadata !15, null, null, null, i32 0, metadata !17} ; [ DW_TAG_subprogram ] [line 3] [static_member_function]
!15 = metadata !{metadata !"0x15\00\000\000\000\000\000\000", i32 0, null, null, metadata !16, null, null, null} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!16 = metadata !{metadata !11}
!17 = metadata !{metadata !"0x24"}                      ; [ DW_TAG_base_type ] [line 0, size 0, align 0, offset 0]
!18 = metadata !{metadata !"0x2e\00static_member_function\00static_member_function\00_ZN1C22static_member_functionEv\0013\000\001\000\006\00256\000\0013", metadata !4, null, metadata !15, null, i32 ()* @_ZN1C22static_member_functionEv, null, metadata !14, metadata !1} ; [ DW_TAG_subprogram ] [line 13] [def] [static_member_function]
!19 = metadata !{metadata !"0x2e\00global_function\00global_function\00_Z15global_functionv\0019\000\001\000\006\00256\000\0019", metadata !4, metadata !4, metadata !15, null, i32 ()* @_Z15global_functionv, null, null, metadata !1} ; [ DW_TAG_subprogram ] [line 19] [def] [global_function]
!20 = metadata !{metadata !"0x2e\00global_namespace_function\00global_namespace_function\00_ZN2ns25global_namespace_functionEv\0024\000\001\000\006\00256\000\0024", metadata !4, metadata !21, metadata !22, null, void ()* @_ZN2ns25global_namespace_functionEv, null, null, metadata !1} ; [ DW_TAG_subprogram ] [line 24] [def] [global_namespace_function]
!21 = metadata !{metadata !"0x39\00ns\0023", metadata !4, null} ; [ DW_TAG_namespace ] [/usr2/kparzysz/s.hex/t/dwarf-public-names.cpp]
!22 = metadata !{metadata !"0x15\00\000\000\000\000\000\000", i32 0, null, null, metadata !23, null, null, null} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!23 = metadata !{null}
!24 = metadata !{metadata !25, metadata !26, metadata !27}
!25 = metadata !{metadata !"0x34\00static_member_variable\00static_member_variable\00_ZN1C22static_member_variableE\007\000\001", metadata !8, metadata !4, metadata !11, i32* @_ZN1C22static_member_variableE, metadata !10} ; [ DW_TAG_variable ] [static_member_variable] [line 7] [def]
!26 = metadata !{metadata !"0x34\00global_variable\00global_variable\00\0017\000\001", null, metadata !4, metadata !8, %struct.C* @global_variable, null} ; [ DW_TAG_variable ] [global_variable] [line 17] [def]
!27 = metadata !{metadata !"0x34\00global_namespace_variable\00global_namespace_variable\00_ZN2ns25global_namespace_variableE\0027\000\001", metadata !21, metadata !4, metadata !11, i32* @_ZN2ns25global_namespace_variableE, null} ; [ DW_TAG_variable ] [global_namespace_variable] [line 27] [def]
!28 = metadata !{metadata !"0x101\00this\0016777225\001088", metadata !3, metadata !4, metadata !29} ; [ DW_TAG_arg_variable ] [this] [line 9]
!29 = metadata !{metadata !"0xf\00\000\0064\0064\000\000", null, null, metadata !8} ; [ DW_TAG_pointer_type ] [line 0, size 64, align 64, offset 0] [from C]
!30 = metadata !{i32 9, i32 0, metadata !3, null}
!31 = metadata !{i32 10, i32 0, metadata !3, null}
!32 = metadata !{i32 11, i32 0, metadata !3, null}
!33 = metadata !{i32 14, i32 0, metadata !18, null}
!34 = metadata !{i32 20, i32 0, metadata !19, null}
!35 = metadata !{i32 25, i32 0, metadata !20, null}
!36 = metadata !{i32 26, i32 0, metadata !20, null}
!37 = metadata !{metadata !"dwarf-public-names.cpp", metadata !"/usr2/kparzysz/s.hex/t"}
!38 = metadata !{i32 1, metadata !"Debug Info Version", i32 2}
