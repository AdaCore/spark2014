procedure Illegal_Assign with SPARK_Mode is
    type List;
    type List_Acc is access List;
    type List is record
       Val  : Integer;
       Next : List_Acc;
    end record;

   function At_End_Borrow (L : access constant List) return access constant List is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   X : List_Acc := new List'(1, null);
   W : List_Acc;
begin
    X.Next := new List'(2, null);
    X.Next.Next := new List'(3, null);
    X.Next.Next.Next := new List'(4, null);
    X.Next.Next.Next.Next := new List'(5, null);

   declare
      Y : access List := X.Next.Next;
   begin
      X.Val := 42; -- ok, X.Val is not borrowed
      pragma Assert (At_End_Borrow (X.Next.Next) /= null); -- ok, we are in a pledge
      pragma Assert (X.Next /= null); -- cannot read X.Next, as it is borrowed
      W := X.Next;    -- cannot move X.Next, as it is borrowed
      X.Next := null; -- cannot write into X.Next, as it is borrowed
   end;

   declare
      Y : access constant List := X.Next.Next;
   begin
      X.Val := 42; -- ok, X.Val is not observed
      pragma Assert (X.Next /= null); -- ok, reads are allowed on observed
      X.Next := null; -- cannot write into X.Next, as it is observed
      W := X.Next;
   end;
end Illegal_Assign;
