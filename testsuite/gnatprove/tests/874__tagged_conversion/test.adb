procedure Test with SPARK_Mode is
   package Nested is
      type Root is tagged null record;
      type Child is new Root with record
         F, G : Integer;
      end record;
   end Nested; use Nested;
   procedure P (A, B : in out Integer) with
     Depends => (A => A, B => B);
   procedure P (A, B : in out Integer) is
      R : Root'Class := Child'(A, B);
   begin
      A := Child (R).F;
      B := Child (R).G;
   end P;

begin
   null;
end;
