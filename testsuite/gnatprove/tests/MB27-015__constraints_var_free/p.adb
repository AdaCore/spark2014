package body P
  with SPARK_Mode => On
is
   procedure Op (A : in out Integer)
   is
      -- A is "in out" so a variable not a constant, therefore...
      subtype LS4 is Integer range A .. 10;   -- illegal
   begin
      A := A + 2;

      --  The range constraint of a loop parameter specification
      --  may contain variables, so
      for I in Integer range 1 .. A loop -- legal
         A := A + 1;
      end loop;

   end Op;
end P;
