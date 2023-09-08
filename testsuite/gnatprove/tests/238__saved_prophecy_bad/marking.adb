procedure Marking with SPARK_Mode is

   type Cell;
   type List is access Cell;
   type CList is access constant Cell;
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

   procedure Bad_Target_Type (Input : List) is
      X : access Cell := Input;
      Y : constant access constant Cell := At_End (X) with Ghost; -- OK
      Z : access constant Cell := At_End (X) with Ghost; -- KO
      T : constant CList := At_End (X) with Ghost; -- KO
      U : access List := At_End (X).Tail.Tail'Access with Ghost; -- KO
      V : access constant Cell := Y with Ghost; -- KO;
   begin
      null;
   end Bad_Target_Type;

   function F (X : access constant Cell)
               return access constant Integer with Ghost;

   function F (X : access constant Cell) return access constant Integer is
   begin
      return X.Tail.Tail.Head'Access;
   end F;

   procedure Bad_Source_Shape (Input : List) is
      X : access Cell := Input;
      Y : constant access constant Integer
        := At_End (X).Head'Access with Ghost; -- OK
      Z : constant access constant List
        := At_End(X).Tail'Access with Ghost; -- OK
      T : constant access constant Integer
        := At_End (X).Tail.Head'Access with Ghost; --  KO, goes through pointer
      U : constant access constant Integer
        := F (At_End (X)) with Ghost;
      --  KO, not a known subcomponent reference
      V : constant access constant Cell
        := At_End (At_End (X)) with Ghost; -- KO
      W : constant access constant Cell := At_End (X).Tail with Ghost;
      -- KO, goes through pointer (implicitly).
      Z_Copy : constant access constant List := Z with Ghost; -- OK
      Z_Bad_Copy : constant access constant List
        := Z.all.Tail'Access with Ghost;
      -- KO, goes through pointer
   begin
      null;
   end Bad_Source_Shape;

begin
   null;
end Marking;
