procedure Repr with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F : Integer;
         G : Integer;
      end record;
      function "=" (X, Y : Root'Class) return Boolean is (X.F = Y.F);
      function F (X, Y, Z : Root'Class) return Boolean is
        (X in Y | Z);
   end Nested;
   use Nested;

   R1 : constant Root := (F => 0, G => 0);
   R2 : constant Root := (F => 0, G => 1);

   RC1 : constant Root'Class := R1;
   RC2 : constant Root'Class := R2;
begin
   --  The overriding of "=" on Root'Class should not be taken into account in
   --  the membership test as class-wide types do not have primitives.
   pragma Assert (F (RC1, RC2, RC2)); --@ASSERT:FAIL
end Repr;
