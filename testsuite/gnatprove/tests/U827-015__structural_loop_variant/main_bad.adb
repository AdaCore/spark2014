with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main_Bad with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   function Rand (I : Integer) return Boolean with Import;
   function Id (L : access constant L_Cell) return access constant L_Cell is (L);
   function Next (L : not null access constant L_Cell) return access constant L_Cell is (L.N);

   function Length_1 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            C := C.all'Access;
         end loop;
      end return;
   end Length_1;

   function Length_2 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            if Rand (1) then
               goto End_Loop;
            end if;
            C := C.N;
            <<End_Loop>>
         end loop;
      end return;
   end Length_2;

   procedure Length_3 (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
         R := R + 1;
         if C.N = null then
            exit;
         else
            C.N := C.N.N; -- @RESOURCE_LEAK:FAIL
         end if;
      end loop;
   end Length_3;

   function Length_4 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            C := Id (C);
         end loop;
      end return;
   end Length_4;

   function Length_5 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            C := C;
         end loop;
      end return;
   end Length_5;

   function Length_6 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            if Rand (5) then
               C := C.N;
            else
               if Rand (4) then
                  if Rand (1) then
                     C := C.N;
                  elsif Rand (2) then
                     return;
                  elsif Rand (3) then
                     null;
                  else
                     C := C.N;
                  end if;
               else
                  C := C.N;
               end if;
            end if;
         end loop;
      end return;
   end Length_6;

   function Length_7 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            case Rand (1) is
               when True => C := C.N;
               when False => null;
            end case;
         end loop;
      end return;
   end Length_7;

   function Length_8 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
            R := R + 1;
            for I in 1 .. 1 loop
               if Rand (1) then
                  goto End_Loop;
               end if;
            end loop;
            C := C.N;
            <<End_Loop>>
         end loop;
      end return;
   end Length_8;

   procedure Length_9 (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
         R := R + 1;
         C.N := new L_Cell'(0, C.N);
         C := C.N;
      end loop;
   end Length_9;

   procedure Length_9_b (L : access L_Cell; R : out Big_Natural) is
      procedure Add_One_Cell (L : access L_Cell) with
        Global => null
      is
      begin
         L.N := new L_Cell'(0, L.N);
      end Add_One_Cell;
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
         R := R + 1;
         Add_One_Cell (C);
         C := C.N;
      end loop;
   end Length_9_b;

   procedure Length_10 (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
      procedure Add_One_Cell with
        Global => (In_Out => C),
        Pre => C /= null,
        Post => C /= null
      is
      begin
         C.N := new L_Cell'(0, C.N);
      end Add_One_Cell;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
         R := R + 1;
         Add_One_Cell;
         C := C.N;
      end loop;
   end Length_10;

   procedure Length_11 (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- @LOOP_VARIANT:FAIL
         R := R + 1;
         declare
            B : access L_Cell := C;
         begin
            B.N := new L_Cell'(0, B.N);
         end;
         C := C.N;
      end loop;
   end Length_11;
begin
   null;
end;
