procedure Main with SPARK_Mode is
   type Cell;
   type List is access Cell;
   type Cell is record
      Head : aliased Integer;
      Tail : aliased List;
   end record;

   function At_End (X : access constant Integer)
                    return access constant Integer is (X)
     with Ghost, Global => null, Annotate => (GNATprove, At_End_Borrow);
   function At_End (X : access constant List)
                    return access constant List is (X)
     with Ghost, Global => null, Annotate => (GNATprove, At_End_Borrow);
   function At_End (X : access constant Cell)
                    return access constant Cell is (X)
     with Ghost, Global => null, Annotate => (GNATprove, At_End_Borrow);

   procedure Skip_Move (X : List) with Pre => X /= null;
   procedure Skip_Borrow (X : List)
     with Pre => X /= null and then X.Tail /= null;
   procedure Re_Borrow (X : List)
     with Pre => X /= null and then X.Tail /= null;

   procedure Skip_Move (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
      U : constant access constant Cell := Z with Ghost;
      V : List := Y.Tail;
   begin
      Y.Tail := new Cell'(Head => 36, Tail => V);
      pragma Assert (
                     (U = null) = (At_End (X) = null)
                     and then (if U /= null
                       then (U.Tail = null) = (At_End (X).Tail = null)
                       and then (if U.Tail /= null
                         then U.Tail.Head = At_End (X).Tail.Head)));
      pragma Assert (U.Tail.Head = 36); --@ASSERT:FAIL
   end Skip_Move;

   procedure Skip_Borrow (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
   begin
      declare
         U : access Cell := Y.Tail;
      begin
         U.Head := 1;
      end;
      pragma Assert (
                     (Z = null) = (At_End (X) = null)
                     and then (if Z /= null
                       then (Z.Tail = null) = (At_End (X).Tail = null)
                       and then (if Z.Tail /= null
                         then Z.Tail.Head = At_End (X).Tail.Head)));
      pragma Assert (Z.Tail.Head = 1); --@ASSERT:FAIL
   end Skip_Borrow;

   procedure Re_Borrow (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
   begin
      Y := Y.Tail;
      pragma Assert (Z /= null);
      pragma Assert ((Z.Tail = null) = (At_End (Y) = null));
      pragma Assert (if Z.Tail /= null then Z.Tail.Head = At_End(Y).Head);
      Y.Head := 0;
      pragma Assert (Z.Tail.Head = 0); --@ASSERT:FAIL
   end;

begin
   null;
end Main;
