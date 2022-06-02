with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

procedure Test_List with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

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

   function At_End (X : access constant List) return access constant List is (X)
     with
       Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   function At_End (X : access constant Integer) return access constant Integer is (X)
     with
       Ghost,
       Annotate => (GNATprove, At_End_Borrow);

   M : Big_Positive := 1 with Ghost;

   function Reference (L : not null access List; N : Big_Positive) return not null access Integer
   with Pre => N <= Length (L.all) and then M <= Length (L.all),
     Post => At_End (Reference'Result).all = Nth_Int (At_End (L).all, N)
     and then (N = M or else Nth_Int (At_End (L).all, M) = Nth_Int (L.all, M))
     and then Length (At_End (L).all) = Length (L.all)
   is
   begin
      if N = 1 then
         return L.V'Access;
      end if;

      declare
         C : not null access List := L.N;
         I : Big_Positive := N - 1;
         J : Big_Integer := M - 1 with Ghost;
      begin
         while I > 1 loop
            pragma Loop_Invariant (N - I = Length (L.all) - Length (C.all));
            pragma Loop_Invariant (M - J = Length (L.all) - Length (C.all));
            pragma Loop_Invariant
              (if I <= Length (At_End (C).all)
               then Nth_Int (At_End (L.N).all, N - 1) = Nth_Int (At_End (C).all, I));
            pragma Loop_Invariant
              (if J <= 0 and M > 1
               then Nth_Int (At_End (L.N).all, M - 1) = Nth_Int (L.all, M));
            pragma Loop_Invariant
              (if J > 0 then Nth_Int (L.all, M) = Nth_Int (C.all, J));
            pragma Loop_Invariant
              (if J > 0 and J <= Length (At_End (C).all) and M > 1
               then Nth_Int (At_End (L.N).all, M - 1) = Nth_Int (At_End (C).all, J));
            pragma Loop_Invariant
              (Length (At_End (L.N).all) = Length (L.N.all) + Length (At_End (C).all) - Length (C.all));
            C := C.N;
            I := I - 1;
            J := J - 1;
         end loop;
         declare
            Res : access Integer := C.all.V'Access;
         begin
            return Res;
         end;
      end;
   end Reference;

   function All_Zeros (L : List) return Boolean is
     (L.V = 0 and then (L.N = null or else All_Zeros (L.N.all)))
   with Ghost,
       Annotate => (GNATprove, Always_Return);

   procedure Set_All_To_Zero (L : aliased in out List)
   with Post => Length (L) = Length (L)'Old
     and then All_Zeros (L)
   is
      B_Init : access List := L'Access;
      B      : access List := B_Init;
   begin
      while B /= null loop
         pragma Loop_Invariant
           (if Length (B.all) = Length (At_End (B).all)
            then Length (B.all)'Loop_Entry = Length (At_End (B_Init).all));
         pragma Loop_Invariant
           (if All_Zeros (At_End (B).all) then All_Zeros (At_End (B_Init).all));
         B.V := 0;
         B := B.N;
      end loop;
   end Set_All_To_Zero;

   procedure Set_One_To_Zero (L : aliased in out List; N : Big_Positive) with
     Pre  => N <= Length (L) and then M <= Length (L),
     Post => Nth_Int (L, N) = 0
     and then Length (L) = Length (L)'Old
     and then (N = M or else Nth_Int (L, M) = Nth_Int (L, M)'Old)
   is
      B_Init : access List := L'Access;
      B      : access Integer := Reference (B_Init, N);
   begin
      B.all := 0;
   end Set_One_To_Zero;
begin
   null;
end Test_List;
