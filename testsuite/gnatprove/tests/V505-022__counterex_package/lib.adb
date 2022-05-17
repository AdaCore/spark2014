package body Lib is

   function Make_Array (X : Integer) return Arr is (others => (F => X));

   function Same (X : Integer := 42) return Integer is (X);

   A : constant Arr := (others => (F => Same));
begin
   pragma Assert (A (Four).F = 0);
end Lib;
