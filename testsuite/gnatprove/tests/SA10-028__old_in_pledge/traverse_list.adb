procedure Traverse_List with SPARK_Mode is

    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

   function Eq (X, Y : access constant List) return Boolean with
     Annotate => (GNATprove, Terminating);
   function "=" (X, Y : List) return Boolean is
     (X.Val = Y.Val and then Eq (X.Next, Y.Next))
   with
     Annotate => (GNATprove, Terminating);
   function Eq (X, Y : access constant List) return Boolean is
     ((X = null) = (Y = null)
      and then (if X /= null then X.all = Y.all));

   procedure Prove_Eq_Refl (X : access constant List) with
     Annotate => (GNATprove, Terminating),
     Ghost,
     Global => null,
     Post => Eq (X, X)
   is
   begin
      if X /= null then
         Prove_Eq_Refl (X.Next);
      end if;
   end Prove_Eq_Refl;

   function At_End_Borrow (L : access constant List) return access constant List is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function Tail (L : access List) return access List with
     Contract_Cases =>
       (L = null =>
          Tail'Result = null and At_End_Borrow (L) = null,
        others   => At_End_Borrow (L).Val = L.Val
          and Eq (At_End_Borrow (L).Next, At_End_Borrow (Tail'Result)));

   function Tail (L : access List) return access List is
   begin
      if L = null then
         return null;
      else
         declare
            Res : access List := L.Next;
         begin
            Prove_Eq_Refl (At_End_Borrow (Res));
            return Res;
         end;
      end if;
   end Tail;

   X : List_Acc := new List'(1, null);
begin
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
end Traverse_List;
