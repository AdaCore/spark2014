procedure Borrow_Checking with SPARK_Mode is

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

   procedure Bad1 (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
      U : access List := Y.Tail'Access;
   begin
      pragma Assert (Z.Tail.Head = 0); -- KO, part of Y is re-borrowed.
   end Bad1;

   procedure Bad2 (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
      U : access Cell := Y;
   begin
      pragma Assert (Z.Tail.Head = 0); -- KO, Y is re-borrowed.
   end Bad2;

   procedure Bad3 (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
      U : constant access constant Cell := Z with Ghost;
      V : List := Y.Tail;
   begin
      pragma Assert (U.Tail.Head = 0); -- KO, part of Y is moved.
      Y.Tail := null;
   end Bad3;

   procedure Skip_Move (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
      U : constant access constant Cell := Z with Ghost;
      V : List := Y.Tail;
   begin
      Y.Tail := null;
      pragma Assert (U.Tail.Head = 0); -- OK, moved part was restored.
   end Skip_Move;

   procedure Skip_Borrow (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
   begin
      declare
         U : access Cell := Y.Tail;
      begin
         U.Tail.Head := 1;
      end;
      pragma Assert (Z.Tail.Head = 0); -- OK, sub-borrow is over.
   end Skip_Borrow;

   procedure Re_Borrow_Ok (X : List) is
      Y : access Cell := X;
      Z : constant access constant Cell := At_End (Y) with Ghost;
   begin
      Y := Y.Tail;
      pragma Assert (Z.Tail.Head = 0); -- OK
   end Re_Borrow_Ok;

begin
   null;
end Borrow_Checking;
