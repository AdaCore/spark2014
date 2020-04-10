procedure Traverse_List with SPARK_Mode is

    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

   function Pledge (Borrower : access constant List; Prop : Boolean) return Boolean is
     (Prop)
   with Ghost,
     Annotate => (GNATprove, Pledge);

   function Tail (L : access List) return access List with
     Contract_Cases =>
       (L = null =>
          Tail'Result = null and Pledge (Tail'Result, L = null),
        others   => Pledge (Tail'Result, L.Val = L.Val'Old)
          and Pledge (Tail'Result, L.Next = Tail'Result));

   function Tail (L : access List) return access List is
   begin
      if L = null then
         return null;
      else
         return L.Next;
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
