with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main with SPARK_Mode is
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
      C : aliased access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            declare
               Incr : constant Big_Integer := 1;
            begin
               R := R + Incr;
               C := C.N;
            end;
         end loop;
      end return;
   end Length_1;

   function Length_2 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- OK, but gotos are not handled precisely
            if Rand (1) then
               goto Before_Next;
            end if;
            R := R + 1;
            <<Before_Next>>
            C := C.N;
         end loop;
      end return;
   end Length_2;

   function Length_2_b (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            C := C.N;
            if Rand (1) then
               goto Before_Next;
            end if;
            R := R + 1;
            <<Before_Next>>
         end loop;
      end return;
   end Length_2_b;

   function Length_3 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            R := R + 1;
            case Rand (1) is
               when True  => exit;
               when False => null;
            end case;
            C := C.N;
         end loop;
      end return;
   end Length_3;

   function Length_4 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- OK, but function calls are not handled precisely
            R := R + 1;
            C := Next (C);
         end loop;
      end return;
   end Length_4;

   function Length_4_b (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            R := R + 1;
            C := Id (C.N);
         end loop;
      end return;
   end Length_4_b;

   function Length_5 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;

      procedure Next with Pre => C /= null, Global => (In_Out => C) is
      begin
         C := C.N;
      end Next;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- OK, but procedure calls are not handled precisely
            R := R + 1;
            Next;
         end loop;
      end return;
   end Length_5;

   function Length_5_b (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;

      procedure Next is
      begin
         C := C.N;
      end Next;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            R := R + 1;
            Next;
         end loop;
      end return;
   end Length_5_b;

   function Length_5_t (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;

      procedure Next with Pre => C /= null, Global => (In_Out => C) is
      begin
         C := C.N;
      end Next;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            R := R + 1;
            Next;
            if C = null then
               exit;
            else
               C := C.N;
            end if;
         end loop;
      end return;
   end Length_5_t;

   function Length_6 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            R := R + 1;
            C := List (C.N);
         end loop;
      end return;
   end Length_6;

   function Length_7 (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C); -- OK, but loops are not handled precisely
            R := R + 1;
            for I in 1 .. 1 loop
               C := List (C.N);
            end loop;
         end loop;
      end return;
   end Length_7;

   function Length_7_b (L : access constant L_Cell) return Big_Natural is
      C : access constant L_Cell := L;
   begin
      return R : Big_Natural := 0 do
         while C /= null loop
            pragma Loop_Variant (Structural => C);
            for I in 1 .. 1 loop
               R := R + To_Big_Integer (I);
            end loop;
            C := List (C.N);
         end loop;
      end return;
   end Length_7_b;

   procedure Length_8 (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C);
         R := R + 1;
         C.V := 0;
         C := C.N;
      end loop;
   end Length_8;

   procedure Length_8_b (L : access L_Cell; R : out Big_Natural) is
      procedure Set_To_Zero (I : out Integer) with Global => null
      is
      begin
         I := 0;
      end Set_To_Zero;
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C);
         R := R + 1;
         Set_To_Zero (C.V);
         C := C.N;
      end loop;
   end Length_8_b;

   procedure Length_9 (L : access L_Cell; R : out Big_Natural) is
      procedure Set_To_Zero (I : not null access L_Cell) with
        Global => null
      is
      begin
         I.V := 0;
      end Set_To_Zero;
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- OK, but procedure calls are not handled precisely
         R := R + 1;
         Set_To_Zero (C);
         C := C.N;
      end loop;
   end Length_9;

   procedure Length_9_b (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
      procedure Set_To_Zero with
        Global => (In_Out => C),
        Pre => C /= null,
        Post => C /= null
      is
      begin
         C.V := 0;
      end Set_To_Zero;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- OK, but procedure calls are not handled precisely
         R := R + 1;
         Set_To_Zero;
         C := C.N;
      end loop;
   end Length_9_b;

   procedure Length_10 (L : access L_Cell; R : out Big_Natural) is
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C);
         R := R + 1;
         declare
            B : access L_Cell := C;
         begin
            B.V := 0;
         end;
         C := C.N;
      end loop;
   end Length_10;

   procedure Length_10_b (L : access L_Cell; R : out Big_Natural) is
      procedure Set_To_Zero (I : out Integer) with Global => null
      is
      begin
         I := 0;
      end Set_To_Zero;
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C);
         R := R + 1;
         declare
            B : access L_Cell := C;
         begin
            Set_To_Zero (B.V);
         end;
         C := C.N;
      end loop;
   end Length_10_b;

   procedure Length_11 (L : access L_Cell; R : out Big_Natural) is
      procedure Set_To_Zero (I : not null access L_Cell) with
        Global => null
      is
      begin
         I.V := 0;
      end Set_To_Zero;
      C : access L_Cell := L;
   begin
      R := 0;
      while C /= null loop
         pragma Loop_Invariant (R >= 0);
         pragma Loop_Variant (Structural => C); -- OK, but procedure calls are not handled precisely
         R := R + 1;
         declare
            B : access L_Cell := C;
         begin
            Set_To_Zero (B);
         end;
         C := C.N;
      end loop;
   end Length_11;
begin
   null;
end;
