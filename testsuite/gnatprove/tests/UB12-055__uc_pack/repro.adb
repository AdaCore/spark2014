with Ada.Unchecked_Conversion;

procedure Repro is
   type Wrapper is record
      C : Character;
   end record with Size => 8;

   type Arr is array (Positive range <>) of Wrapper;
   subtype Subarr is Arr(1..4);

   function To_Int is new Ada.Unchecked_Conversion (Subarr, Integer);

   X : Subarr := (others => (C => ASCII.NUL));
   Y : Integer := To_Int (X);
begin
   pragma Assert (Y = 0);
end Repro;
