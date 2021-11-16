procedure Repr with SPARK_Mode is
   function Rand (X : Integer) return Boolean with Import;

   package Nested is
      type Root is tagged record
         F : Integer;
         G : Integer;
      end record;
      function "=" (X, Y : Root) return Boolean is (X.F = Y.F);
      function F (X, Y, Z : Root'Class) return Boolean is
        (X in Y | Z);
      type Child is new Root with null record;
      function "=" (X, Y : Child) return Boolean is (X.F = Y.F and X.G = Y.G);
   end Nested;
   use Nested;

   R1 : constant Root := (F => 0, G => 0);
   R2 : constant Root := (F => 0, G => 1);

   RC1 : constant Root'Class := R1;
   RC2 : constant Root'Class := R2;

   C1 : constant Child := (F => 0, G => 0);
   C2 : constant Child := (F => 0, G => 1);

   CC1 : constant Root'Class := C1;
   CC2 : constant Root'Class := C2;
begin
   if Rand (1) then
      pragma Assert (not F (RC1, RC2, RC2)); --@ASSERT:FAIL
   elsif Rand (2) then
      pragma Assert (F (CC1, CC2, CC2)); --@ASSERT:FAIL
   else
      pragma Assert (F (RC1, CC2, CC2)); --@ASSERT:FAIL
   end if;
end Repr;
