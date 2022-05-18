with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   function At_End (L : access constant L_Cell) return access constant L_Cell is (L)
     with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Length (L : access constant L_Cell) return Big_Natural is
     (if L = null then Big_Natural'(0) else Length (L.N) + 1)
   with Ghost, Annotate => (GNATprove, Always_Return);

   function All_Zero (L : access constant L_Cell) return Boolean is
     (L = null or else (L.V = 0 and then All_Zero (L.N)))
   with Ghost, Subprogram_Variant => (Decreases => Length (L));

   procedure Set_All_To_Zero (L : List) with
     Post => All_Zero (L)
   is
      X : access L_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Invariant
           (if All_Zero (At_End (X)) then All_Zero (At_End (L)));
         pragma Loop_Variant (Decreases => Length (X));
         X.V := 0;
         pragma Assert (Length (X) > Length (X.N));
         X := X.N;
      end loop;
   end Set_All_To_Zero;

   function All_Zero_Bad (L : access constant L_Cell) return Boolean is
     (L = null or else (L.V = 0 and then All_Zero_Bad (L.N)))
   with Ghost, Subprogram_Variant => (Decreases => Length (L) - 1); --@RANGE_CHECK:FAIL

   procedure Set_All_To_Zero_Bad (L : List)
   is
      X : access L_Cell := L;
   begin
      while X /= null loop
         pragma Loop_Variant (Decreases => Length (X) - 2); --@RANGE_CHECK:FAIL
         X.V := 0;
         pragma Assert (Length (X) > Length (X.N));
         X := X.N;
      end loop;
   end Set_All_To_Zero_Bad;
begin
   null;
end;
