procedure Discr_Dyn is

   FUNCTION IDENT_INT (X : INTEGER) RETURN INTEGER IS
   BEGIN
      RETURN X;                -- ALWAYS EXECUTED.
   END IDENT_INT;

   SUBTYPE STB IS INTEGER RANGE 1 .. 10;
   TYPE TB IS ARRAY(STB RANGE <>) OF INTEGER;
   TYPE R2 (A : STB) IS
      RECORD
         B : TB(1 .. A);
         C : BOOLEAN;
      END RECORD;
   B1 : R2(IDENT_INT(3)) := (IDENT_INT(2), (-1, -2), FALSE);
begin
   null;
end;
