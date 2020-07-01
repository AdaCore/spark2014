procedure Tagged_Type with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F, G : Integer;
      end record;

      function "=" (X, Y : Root) return Boolean is (X.F = Y.F);

      type Child is new Root with record
         H : Integer;
      end record;

      function "=" (X, Y : Child) return Boolean is (X.F = Y.F and X.H = Y.H);
   end Nested;
   use Nested;

   R : Root'Class := Root'(1, 2);
   C : Root'Class := Root'Class (Child'(1, 2, 3));
begin
   pragma Assert (R /= C);
end Tagged_Type;
