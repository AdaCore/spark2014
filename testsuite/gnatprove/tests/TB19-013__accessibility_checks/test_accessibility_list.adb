with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Test_Accessibility_List with SPARK_Mode is
   type List;
   type List_Acc is access List;
   type List is record
      V : aliased Integer;
      N : List_Acc;
   end record;

   function Length (L : List) return Big_Positive is
     (if L.N = null then Big_Positive'(1) else Length (L.N.all) + 1)
   with Ghost,
       Annotate => (GNATprove, Always_Return);

   function Nth_Int (L : List; N : Big_Positive) return Integer is
     (if N = 1 then L.V else Nth_Int (L.N.all, N - 1))
   with Ghost,
       Annotate => (GNATprove, Always_Return),
       Pre => N <= Length (L);

   function Nth (L : aliased List; N : Big_Positive) return not null access constant Integer
   with Pre => N <= Length (L),
     Post => Nth'Result.all = Nth_Int (L, N)
   is
   begin
      if N = 1 then
         return L.V'Access; -- @ACCESSIBILITY_CHECK:NONE
      end if;

      declare
         C : not null access constant List := L.N;
         I : Big_Positive := N - 1;
      begin
         while I > 1 loop
            pragma Loop_Invariant (I <= Length (C.all));
            pragma Loop_Invariant (Nth_Int (L, N) = Nth_Int (C.all, I));
            C := C.N;
            I := I - 1;
         end loop;
         declare
            Res : access constant Integer := C.all.V'Access;
         begin
            return Res; -- @ACCESSIBILITY_CHECK:NONE
         end;
      end;
   end Nth;

   function Nth_Bad (L : aliased List; N : Big_Positive) return not null access constant Integer
   with Pre => N <= Length (L),
     Post => Nth_Bad'Result.all = Nth_Int (L, N)
   is
      C : not null access constant List := L'Access;
      I : Big_Positive := N;
   begin
      while I > 1 loop
         pragma Loop_Invariant (I <= Length (C.all));
         pragma Loop_Invariant (Nth_Int (L, N) = Nth_Int (C.all, I));
         C := C.N;
         I := I - 1;
      end loop;
      declare
         Res : access constant Integer := C.all.V'Access;
      begin
         return Res; -- @ACCESSIBILITY_CHECK:FAIL
      end;
   end Nth_Bad;
begin
   null;
end Test_Accessibility_List;
