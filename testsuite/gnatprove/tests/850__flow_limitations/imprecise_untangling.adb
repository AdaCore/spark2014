procedure Imprecise_Untangling with SPARK_Mode is
   package Nested is
      type Root is tagged null record;
      type Child is new Root with record
         F, G : Integer;
      end record;
   end Nested; use Nested;
   procedure P (A, B : in out Integer) with Pre => True;
   procedure P (A, B : in out Integer) is
      R : Root'Class := Child'(A, B);
   begin
      A := Child (R).F;
      B := Child (R).G;
   end P;
   A, B : Integer;
begin
   P (A, B);
end Imprecise_Untangling;
