with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

procedure Main_Illegal with SPARK_Mode is
   type L_Cell;
   type List is access L_Cell;
   type L_Cell is record
      V : Integer;
      N : List;
   end record;

   procedure All_To_Zero_1 (L : not null access L_Cell)
   with Subprogram_Variant => (Structural => L.N);

   procedure All_To_Zero_1 (L : not null access L_Cell) is
   begin
      L.V := 0;
      if L.N /= null then
         All_To_Zero_1 (L.N);
      end if;
   end All_To_Zero_1;

   procedure Upper_2 (LL : in out List) with Global => null is
      L : List;
      procedure All_To_Zero_2
        with Subprogram_Variant => (Structural => L);

      procedure All_To_Zero_2 is
      begin
         if L /= null then
            L.V := 0;
            L := L.N;
            All_To_Zero_2;
         end if;
      end All_To_Zero_2;
   begin
      L := LL;
      All_To_Zero_2;
      LL := null;
   end Upper_2;

   procedure Upper_3 (L : in out List) with Global => null is
      procedure All_To_Zero_3
        with Subprogram_Variant => (Structural => L);

      procedure All_To_Zero_3 is
      begin
         if L /= null then
            L.V := 0;
            L := L.N;
            All_To_Zero_3;
         end if;
      end All_To_Zero_3;
   begin
      All_To_Zero_3;
   end Upper_3;
begin
   null;
end;
