with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main_Illegal with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   procedure Length (L : access L_Cell; R : out Big_Natural) is
      C : aliased access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C.N); -- Illegal loop variant
         R := R + 1;
         if C.N = null then
            exit;
         else
            C.N := C.N.N;
         end if;
      end loop;
   end Length;
begin
   null;
end;
