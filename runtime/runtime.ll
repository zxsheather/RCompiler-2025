@.int_fmt = private unnamed_addr constant [3 x i8] c"%d\00"

declare i32 @scanf(i8*, ...)

define i32 @getInt() {
entry:
  %value_ptr = alloca i32, align 4
  %fmt_ptr = getelementptr inbounds [3 x i8], [3 x i8]* @.int_fmt, i32 0, i32 0
  %read = call i32 (i8*, ...) @scanf(i8* %fmt_ptr, i32* %value_ptr)
  %ok = icmp eq i32 %read, 1
  br i1 %ok, label %loaded, label %fallback

loaded:
  %value = load i32, i32* %value_ptr, align 4
  ret i32 %value

fallback:
  ret i32 0
}

declare i32 @fflush(i8*)
declare void @_exit(i32)

define i32 @exit(i32 %code) {
entry:
  %_ = call i32 @fflush(i8* null)
  call void @_exit(i32 %code)
  ret i32 %code
}
