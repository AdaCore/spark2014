procedure C37102B is

   FUNCTION IDENT_INT       -- AN IDENTITY FUNCTION FOR TYPE INTEGER.
      ( X : INTEGER         -- THE ARGUMENT.
      ) RETURN INTEGER      -- X.
   IS (X) WITH GLOBAL => NULL;

   function F (D : Integer) return Integer is
   begin
      return IDENT_INT (D);
   end F;

   type ARR is array (Integer range <>) of Integer;

   G : Integer := 0;

   type Q is record
      K : ARR (1 .. F (D => G));
   end record;

   type R is new ARR (1 .. F (D => G));

begin
   null;
end C37102B;
