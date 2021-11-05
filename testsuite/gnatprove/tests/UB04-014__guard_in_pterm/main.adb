with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   function B_Length (L : access constant L_Cell) return Big_Natural is
     (if L = null then Big_Natural'(0) else B_Length (L.N) + 1)
   with Ghost, Annotate => (GNATprove, Terminating);

   function Length (L : access constant L_Cell) return Natural is
     (if L = null then 0 else Length (L.N) + 1)
   with Ghost, Annotate => (GNATprove, Terminating),
       Pre => B_Length (L) <= To_Big_Integer (Natural'Last),
       Post => To_Big_Integer (Length'Result) = B_Length (L);

   procedure Set_All_To_Zero (L : List) with
     Pre => B_Length (L) <= To_Big_Integer (Natural'Last)
   is
      X : access L_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Invariant
           (B_Length (X) <= To_Big_Integer (Natural'Last));
         pragma Loop_Variant (Decreases => Length (X));
         X.V := 0;
         X := X.N;
      end loop;
   end Set_All_To_Zero;
begin
   null;
end;
