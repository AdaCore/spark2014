procedure Main with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F : Integer;
         D : Natural;
      end record;
      function "=" (X, Y : Root) return Boolean is (X.F = Y.F);

      type Child is new Root with record
         G : Integer;
      end record;
   end Nested;
   use Nested;

   function Rand (X : Natural) return Natural with
     Import,
     Post => Rand'Result in 1 .. 2;
   type Root_Acc is access all Root'Class;
   type Root_Array is array (Positive range <>) of Root_Acc;

   R1 : aliased Root'Class := Root'(F => 1, D => 1);
   R2 : aliased Root'Class := Root'(F => 1, D => 2);
   A1 : Root_Acc := R1'Access;
   A2 : Root_Acc := R2'Access;
   A  : Root_Array := (1 => A1, 2 => A2);
   RR : Root'Class := Root'(F => 1, D => 3);
   RC : Root'Class := Child'(F => 1, G => 0, D => 4);

begin
   --  R1, R2, and RR have the same F field, they are equal
   pragma Assert (A (Rand (1)).all = RR);

   --  R1, R2, and RC have the same F field, their Root parts are equal
   pragma Assert (Root (A (Rand (2)).all) = Root (RC));

   --  R1, R2, and RC do not have the same tag, they are not equal
   pragma Assert (A (Rand (3)).all = RC); -- @ASSERT:FAIL
end Main;
