with Ada.Unchecked_Deallocation;
procedure Main with SPARK_Mode is
   type AInt is access Integer;
   type AAInt is access AInt;
   function Allocate return AAInt is
     (new AInt'(new Integer'(0)));
   procedure Deallocate is new Ada.Unchecked_Deallocation (Integer, AInt);
   Y : AAInt := Allocate; --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
begin
   declare
      Z : access AInt := Y.all'Access;
   begin
      Deallocate (Z.all);
   end;
end Main;
