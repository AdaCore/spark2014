with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   function Length_5 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;

      procedure Next with Pre => C /= null, Global => (In_Out => C) is
      begin
         C := C.N;
      end Next;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            R := R + 1;
            Next;
         end loop;
      end return;
   end Length_5;
begin
   null;
end;
