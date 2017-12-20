with Interfaces; use Interfaces;

with Output;

procedure Main
with
   SPARK_Mode
is
   subtype Word64_Pos is Unsigned_64 range 0 .. 63;

   function To_Pos (Value : Unsigned_64) return Word64_Pos
   is
   begin
      return Word64_Pos'Mod (Value);  --  @RANGE_CHECK:FAIL
   end To_Pos;
begin
   Output.Print_Result (Unsigned_64 (To_Pos (Value => Unsigned_64'Last)));
end Main;
