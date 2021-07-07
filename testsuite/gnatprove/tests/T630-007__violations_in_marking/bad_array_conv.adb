with Interfaces; use Interfaces;
procedure Bad_Array_Conv with SPARK_Mode is
   type Array_1 is array (Integer_8 range <>) of Natural;
   type Array_2 is array (Unsigned_8 range <>) of Natural;

   X : Array_1 (1 .. 15) := (others => 0);
   Y : Array_2 := Array_2 (X);
begin
   pragma Assert (for all E of Y => E = 0);
end Bad_Array_Conv;
