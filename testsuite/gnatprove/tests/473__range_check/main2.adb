with Interfaces; use Interfaces;

procedure Main2 (Cond : Boolean)
with
    SPARK_Mode
is

   procedure Incr (Data : in out Integer_64) with Global => null;
   procedure Incr (Data : in out Integer_64) is
   begin
      Data := Data + 1;
   end Incr;

   Value128 : Integer_128 := Integer_128'Last;
   Value32  : Integer_32 := Integer_32'Last;
begin
   if Cond then
      Incr (Data => Integer_64 (Value128)); --@RANGE_CHECK:FAIL
   else
      Incr (Data => Integer_64 (Value32)); --@RANGE_CHECK:FAIL
   end if;
end Main2;
