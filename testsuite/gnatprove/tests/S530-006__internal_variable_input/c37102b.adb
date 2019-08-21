procedure C37102B is

   FUNCTION IDENT_INT       -- AN IDENTITY FUNCTION FOR TYPE INTEGER.
      ( X : INTEGER         -- THE ARGUMENT.
      ) RETURN INTEGER      -- X.
   IS (X) WITH GLOBAL => NULL;

   G : Integer := 0;
   --  variable input

   function F (D : Integer) return Integer is
   begin
      return IDENT_INT (G);
   end F;

   type ARR is array (Integer range <>) of Integer;

   K : ARR (1 .. F (D => 5));
   --  variable input in object's type constraint

begin
   null;
end C37102B;
