; ModuleID = 'test1.c'
source_filename = "test1.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @test() #0 {
entry:
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %c = alloca i32, align 4
  %e = alloca i32, align 4
  %0 = load i32, ptr %b, align 4
  %1 = load i32, ptr %c, align 4
  %add = add nsw i32 %0, %1
  store i32 %add, ptr %e, align 4
  %2 = load i32, ptr %e, align 4
  %cmp = icmp sgt i32 %2, 0
  br i1 %cmp, label %if.then, label %if.else

if.then:                                          ; preds = %entry
  %3 = load i32, ptr %a, align 4
  store i32 %3, ptr %e, align 4
  br label %if.end

if.else:                                          ; preds = %entry
  %4 = load i32, ptr %b, align 4
  %5 = load i32, ptr %c, align 4
  %add1 = add nsw i32 %4, %5
  store i32 %add1, ptr %a, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  %6 = load i32, ptr %e, align 4
  %7 = load i32, ptr %c, align 4
  %add2 = add nsw i32 %6, %7
  store i32 %add2, ptr %a, align 4
  ret void
}

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 15.0.0 (git@github.com:llvm/llvm-project.git 4ba6a9c9f65bbc8bd06e3652cb20fd4dfc846137)"}
