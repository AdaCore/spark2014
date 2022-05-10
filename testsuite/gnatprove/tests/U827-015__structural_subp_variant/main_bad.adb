with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main_Bad with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   function Length_1 (L : access constant L_Cell) return Big_Natural
   with Subprogram_Variant => (Structural => L);

   function Length_1 (L : access constant L_Cell) return Big_Natural is
      (if L = null then Length_1 (null) else 1 + Length_1 (L.N)); -- @SUBPROGRAM_VARIANT:FAIL

   function Length_2 (L : access constant L_Cell) return Big_Natural
   with Subprogram_Variant => (Structural => L);

   function Length_2 (L : access constant L_Cell) return Big_Natural is
      (if L = null then Big_Natural'(0) else 1 + Length_2 (L)); -- @SUBPROGRAM_VARIANT:FAIL

   function Length_3 (L : access constant L_Cell) return Big_Natural
   with Subprogram_Variant => (Structural => L);

   function Length_3 (L : access constant L_Cell) return Big_Natural is
      (if L = null then Length_3 (null) else 1 + Length_3 (L.N)); -- @SUBPROGRAM_VARIANT:FAIL

   function Length_4 (L : access constant L_Cell) return Big_Natural
   with Subprogram_Variant => (Structural => L);

   function Length_4_Ann (I : Big_Natural) return Big_Natural
   with Subprogram_Variant => (Structural => I);

   function Length_4 (L : access constant L_Cell) return Big_Natural is
      (if L = null then Big_Natural'(0) else Length_4_Ann (1 + Length_4 (L.N))); -- @SUBPROGRAM_VARIANT:FAIL

   function Length_4_Ann (I : Big_Natural) return Big_Natural is
      (I + Length_4 (null)); -- @SUBPROGRAM_VARIANT:FAIL

   procedure All_To_Zero_1 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_1 (L : access L_Cell) is
   begin
      if L = null then
         return;
      else
         L.V := 0;
         L.N := new L_Cell'(0, L.N);
         All_To_Zero_1 (L.N); -- @SUBPROGRAM_VARIANT:FAIL
      end if;
   end All_To_Zero_1;

   procedure All_To_Zero_2 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_2 (L : access L_Cell) is
   begin
      if L = null then
         return;
      else
         L.V := 0;
         declare
            B : access L_Cell := L;
         begin
            B.N := new L_Cell'(0, B.N);
            All_To_Zero_2 (B.N); -- @SUBPROGRAM_VARIANT:FAIL
         end;
      end if;
   end All_To_Zero_2;

   procedure All_To_Zero_2_b (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_2_b (L : access L_Cell) is
   begin
      if L /= null then
         L.N := new L_Cell'(0, L.N);
      end if;

      if L = null then
         return;
      elsif L.N /= null then
         L.V := 0;
         declare
            B : access L_Cell := L;
         begin
            All_To_Zero_2_b (B.N); -- @SUBPROGRAM_VARIANT:FAIL
         end;
      else
         L.V := 0;
      end if;
   end All_To_Zero_2_b;

   procedure All_To_Zero_3 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_3 (L : access L_Cell) is
   begin
      for I in 1 .. 2 loop
         pragma Loop_Invariant (True);
         if L = null then
            return;
         else
            L.V := 0;
            if L.N /= null then
               declare
                  B : access L_Cell := L.N;
               begin
                  All_To_Zero_3 (B); -- @SUBPROGRAM_VARIANT:FAIL
               end;
            end if;
            L.N := new L_Cell'(0, L.N);
         end if;
      end loop;
   end All_To_Zero_3;

   procedure All_To_Zero_4 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_4 (L : access L_Cell) is
      B : access L_Cell := L;
   begin
      if B = null then
         return;
      end if;

      case B.N = null is
         when True =>
            B.V := 0;
            B := B.N;
            return;
         when False =>
            B.V := 0;
            All_To_Zero_4 (B); -- @SUBPROGRAM_VARIANT:FAIL
      end case;
   end All_To_Zero_4;

   procedure All_To_Zero_5 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_5 (L : access L_Cell) is
      B : access L_Cell := L;
   begin
      if B = null then
         return;
      else
         B.V := 0;
         if B.N = null then
            B := B.N;
            return;
         else
            declare
               B2 : access L_Cell := B;
            begin
               All_To_Zero_5 (B2); -- @SUBPROGRAM_VARIANT:FAIL
            end;
         end if;
      end if;
   end All_To_Zero_5;
begin
   null;
end;
