procedure P is
   type T is record
      Comp : Integer;
   end record;

   V : Integer := 0;
   C : constant T := (Comp => V);
   --  Constant BOTH with variable input and of a record type

   subtype ST is T with Predicate => ST = C;
   --  Subtype referencing that constant; to be used in membership test

   function Test (X : T) return Boolean is (X in ST) with Global => C;
   --  This is equivalent to "X.Comp = C.Comp" and clearly reads C as a Global

begin
   null;
end;
