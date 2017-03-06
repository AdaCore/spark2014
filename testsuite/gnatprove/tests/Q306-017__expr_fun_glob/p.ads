package P is

   X : Integer := 0;
   --  X is referenced by the functions below, but not included in their
   --  explicit Global contracts.

   function F return Boolean is (X = 0) with Global => null;
   --  Reference to X in expression function body

   function B return Boolean with Post => X = 0, Global => null;
   --  Reference to X in Post expression

end;
