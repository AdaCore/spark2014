with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   function Length_1 (L : access constant L_Cell) return Big_Natural
   with Subprogram_Variant => (Structural => L);

   function Length_1 (L : access constant L_Cell) return Big_Natural is
      (if L = null then Big_Natural'(0) else 1 + Length_1 (L.N));

   procedure All_To_Zero_1 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_1 (L : access L_Cell) is
   begin
      if L = null then
         return;
      else
         L.V := 0;
         All_To_Zero_1 (L.N);
      end if;
   end All_To_Zero_1;

   procedure All_To_Zero_1_b (L : in out List)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_1_b (L : in out List) is
   begin
      case L = null is
         when True =>
            L := null;
            return;
         when False =>
            L.V := 0;
            All_To_Zero_1_b (L.N);
      end case;
   end All_To_Zero_1_b;

   procedure All_To_Zero_2 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_2 (L : access L_Cell) is
   begin
      if L = null then
         return;
      else
         L.V := 0;
         declare
            B : access L_Cell := L.N;
         begin
            All_To_Zero_2 (B);
         end;
      end if;
   end All_To_Zero_2;

   procedure All_To_Zero_3 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_3 (L : access L_Cell) is
   begin
      if L = null then
         return;
      elsif L.N = null then
         L.V := 0;
         L.N := new L_Cell'(0, L.N);
      else
         L.V := 0;
         declare
            B : access L_Cell := L.N;
         begin
            All_To_Zero_3 (B);
            B.N := new L_Cell'(0, B.N);
         end;
      end if;
   end All_To_Zero_3;

   procedure All_To_Zero_3_b (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_3_b (L : access L_Cell) is
   begin
      if L = null then
         return;
      elsif L.N /= null then
         L.V := 0;
         declare
            B : access L_Cell := L.N;
         begin
            All_To_Zero_3_b (B);
            B.N := new L_Cell'(0, B.N);
         end;
      else
         L.V := 0;
         L.N := new L_Cell'(0, L.N);
      end if;
   end All_To_Zero_3_b;

   procedure All_To_Zero_4 (L : access L_Cell)
   with Subprogram_Variant => (Structural => L);

   procedure All_To_Zero_4 (L : access L_Cell) is
      B : access L_Cell := L;
   begin
      if B = null then
         return;
      else
         B.V := 0;
         B := B.N;
         if B = null then
            return;
         else
            declare
               B2 : access L_Cell := B;
            begin
               All_To_Zero_4 (B2);
            end;
         end if;
      end if;
   end All_To_Zero_4;
begin
   null;
end;
