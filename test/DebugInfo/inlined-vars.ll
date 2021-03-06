; RUN: %llc_dwarf -O0 < %s | FileCheck %s -check-prefix ARGUMENT
; RUN: %llc_dwarf -O0 < %s | FileCheck %s -check-prefix VARIABLE
; PR 13202

define i32 @main() uwtable {
entry:
  tail call void @llvm.dbg.value(metadata !1, i64 0, metadata !18, metadata !{metadata !"0x102"}), !dbg !21
  tail call void @llvm.dbg.value(metadata !1, i64 0, metadata !22, metadata !{metadata !"0x102"}), !dbg !23
  tail call void @smth(i32 0), !dbg !24
  tail call void @smth(i32 0), !dbg !25
  ret i32 0, !dbg !19
}

declare void @smth(i32)

declare void @llvm.dbg.value(metadata, i64, metadata, metadata) nounwind readnone

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!27}

!0 = metadata !{metadata !"0x11\004\00clang version 3.2 (trunk 159419)\001\00\000\00\000", metadata !26, metadata !2, metadata !2, metadata !3, metadata !2,  metadata !2} ; [ DW_TAG_compile_unit ]
!1 = metadata !{i32 0}
!2 = metadata !{}
!3 = metadata !{metadata !5, metadata !10}
!5 = metadata !{metadata !"0x2e\00main\00main\00\0010\000\001\000\006\00256\001\0010", metadata !26, metadata !6, metadata !7, null, i32 ()* @main, null, null, metadata !2} ; [ DW_TAG_subprogram ]
!6 = metadata !{metadata !"0x29", metadata !26} ; [ DW_TAG_file_type ]
!7 = metadata !{metadata !"0x15\00\000\000\000\000\000\000", null, null, null, metadata !8, null, null, null} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!8 = metadata !{metadata !9}
!9 = metadata !{metadata !"0x24\00int\000\0032\0032\000\000\005", null, null} ; [ DW_TAG_base_type ]
!10 = metadata !{metadata !"0x2e\00f\00f\00_ZL1fi\003\001\001\000\006\00256\001\003", metadata !26, metadata !6, metadata !11, null, null, null, null, metadata !13} ; [ DW_TAG_subprogram ]
!11 = metadata !{metadata !"0x15\00\000\000\000\000\000\000", null, null, null, metadata !12, null, null, null} ; [ DW_TAG_subroutine_type ] [line 0, size 0, align 0, offset 0] [from ]
!12 = metadata !{metadata !9, metadata !9}
!13 = metadata !{metadata !15, metadata !16}
!15 = metadata !{metadata !"0x101\00argument\0016777219\000", metadata !10, metadata !6, metadata !9} ; [ DW_TAG_arg_variable ]

; Two DW_TAG_formal_parameter: one abstract and one inlined.
; ARGUMENT: {{.*Abbrev.*DW_TAG_formal_parameter}}
; ARGUMENT: {{.*Abbrev.*DW_TAG_formal_parameter}}
; ARGUMENT-NOT: {{.*Abbrev.*DW_TAG_formal_parameter}}

!16 = metadata !{metadata !"0x100\00local\004\000", metadata !10, metadata !6, metadata !9} ; [ DW_TAG_auto_variable ]

; Two DW_TAG_variable: one abstract and one inlined.
; VARIABLE: {{.*Abbrev.*DW_TAG_variable}}
; VARIABLE: {{.*Abbrev.*DW_TAG_variable}}
; VARIABLE-NOT: {{.*Abbrev.*DW_TAG_variable}}

!18 = metadata !{metadata !"0x101\00argument\0016777219\000", metadata !10, metadata !6, metadata !9, metadata !19} ; [ DW_TAG_arg_variable ]
!19 = metadata !{i32 11, i32 10, metadata !5, null}
!21 = metadata !{i32 3, i32 25, metadata !10, metadata !19}
!22 = metadata !{metadata !"0x100\00local\004\000", metadata !10, metadata !6, metadata !9, metadata !19} ; [ DW_TAG_auto_variable ]
!23 = metadata !{i32 4, i32 16, metadata !10, metadata !19}
!24 = metadata !{i32 5, i32 3, metadata !10, metadata !19}
!25 = metadata !{i32 6, i32 3, metadata !10, metadata !19}
!26 = metadata !{metadata !"inline-bug.cc", metadata !"/tmp/dbginfo/pr13202"}
!27 = metadata !{i32 1, metadata !"Debug Info Version", i32 2}
