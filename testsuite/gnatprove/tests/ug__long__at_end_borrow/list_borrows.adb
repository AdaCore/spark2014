with SPARK.Big_Integers;  use SPARK.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;
with Lists;               use Lists;

procedure List_Borrows with SPARK_Mode is

   function Length (L : access constant List) return Big_Natural is
     (if L = null then 0 else Length (L.Next) + 1)
   with Subprogram_Variant => (Structural => L);

   function Get (L : access constant List; P : Big_Positive) return Integer is
     (if P = Length (L) then L.Val else Get (L.Next, P))
   with Subprogram_Variant => (Structural => L),
     Pre => P <= Length (L);

   function Eq (L, R : access constant List) return Boolean is
     (Length (L) = Length (R)
      and then (for all P in Interval'(1, Length (L)) => Get (L, P) = Get (R, P)))
   with Annotate => (GNATprove, Inline_For_Proof);

   function Tail (L : access List) return access List with
     Contract_Cases =>
       (L = null =>
          Tail'Result = null and At_End_Borrow (L) = null,
        others   => At_End_Borrow (L).Val = L.Val
          and Eq (L.Next, Tail'Result)
          and Eq (At_End_Borrow (L).Next, At_End_Borrow (Tail'Result)));
   --  No matter what is done later with the result of Tail, at the end of the
   --  borrow L.Val will be the current value of L.Val and the remainder of the
   --  list will be the (updated) value of Tail'Result.

   function Tail (L : access List) return access List is
   begin
      if L = null then
         return null;
      else
         return L.Next;
      end if;
   end Tail;

   procedure Set_All_To_Zero (L : access List) with
     Post => Length (L) = Length (L)'Old
     and then (for all P in Interval'(1, Length (L)) => Get (L, P) = 0);

   procedure Set_All_To_Zero (L : access List) is
      X : access List := L;
      C : Big_Natural := 0 with Ghost;
      --  Number of traversed elements

   begin
      while X /= null loop
         pragma Loop_Invariant (C = Length (X)'Loop_Entry - Length (X));
         --  C is the number of traversed elements
         pragma Loop_Invariant
           (Length (At_End_Borrow (L)) = C + Length (At_End_Borrow (X)));
         --  At the end of the borrow, L will have C more elements than X
         pragma Loop_Invariant
           (for all P in Interval'(1, Length (At_End_Borrow (L))) =>
                (if P <= Length (At_End_Borrow (X))
                 then Get (At_End_Borrow (L), P) = Get (At_End_Borrow (X), P)
                 else Get (At_End_Borrow (L), P) = 0));
         --  At the end of the borrow, the tail of L will be X and the rest
         --  will contain zeros.

         X.Val := 0;
         X := X.Next; --  Reborrow
         C := C + 1;
      end loop;
   end Set_All_To_Zero;

   X : List_Acc;
begin
   X := new List'(1, null);
   X.Next := new List'(2, null);
   X.Next.Next := new List'(3, null);
   X.Next.Next.Next := new List'(4, null);
   X.Next.Next.Next.Next := new List'(5, null);

   declare
      Y : access List := Tail (Tail (X));
   begin
      Y.Val := 42;
   end;

   pragma Assert (X.Val = 1);
   pragma Assert (X.Next.Val = 2);
   pragma Assert (X.Next.Next.Val = 42);
   pragma Assert (X.Next.Next.Next.Val = 4);
end List_Borrows;
