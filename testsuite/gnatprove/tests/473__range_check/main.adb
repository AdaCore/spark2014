with Interfaces; use Interfaces;

procedure Main (Cond : Boolean)
with
    SPARK_Mode
is

   procedure Incr (Data : in out Unsigned_64) with Global => null;
   procedure Incr (Data : in out Unsigned_64) is
   begin
      Data := Data + 1;
   end Incr;

   Value128 : Unsigned_128 := Unsigned_128'Last;
   Value32  : Unsigned_32 := Unsigned_32'Last;
begin
   if Cond then
      Incr (Data => Unsigned_64 (Value128)); --@RANGE_CHECK:FAIL
   else
      Incr (Data => Unsigned_64 (Value32)); --@RANGE_CHECK:FAIL
   end if;
end Main;
