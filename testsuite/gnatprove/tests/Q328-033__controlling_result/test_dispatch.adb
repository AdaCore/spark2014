with Dispatch; use Dispatch;
procedure Test_Dispatch with SPARK_Mode is
   R : Root;
   C : Nested.Child;
   RC : Root'Class := R;
   CC : Root'Class := C;
begin
   RC := Init;
   CC := Init;
   pragma Assert (RC.F = CC.F); --@ASSERT:FAIL
end Test_Dispatch;
