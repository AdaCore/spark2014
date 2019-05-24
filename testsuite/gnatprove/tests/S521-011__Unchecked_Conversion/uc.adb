with Ada.Unchecked_Conversion;

procedure UC with SPARK_Mode is
   type T is array (0 .. 3) of Character;
   function Conv is new Ada.Unchecked_Conversion (T, Integer);
   X : T;
begin
   pragma Assert (X'Size = Conv(X)'Size);
end UC;
