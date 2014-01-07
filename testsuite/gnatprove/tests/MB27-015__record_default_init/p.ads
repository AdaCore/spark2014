with FSB;

--  MB27-015__record_default_init
--
--  Test cases for default initializing expressions of record types
--
--  Demonstrates SPARK LRM 4.4(2)

package P
  with SPARK_Mode => On
is
   -- TU: 2. The ``default_expression`` of a ``component_declaration`` shall not
   -- have any variable inputs.

   -- Case 1 - all literal default expressions. OK
   type R1 is record
      A : Integer := 0;
      B : Boolean := False;
   end record;

   -- Case 2 - default expression directly refs a variable. Illegal
   type R2 is record
      A : Integer := FSB.S; -- illegal
      B : Boolean := False;
   end record;

   -- Case 3 - default expression directly refs a variable
   -- as part of a larger expression. Illegal
   type R3 is record
      A : Integer := FSB.S + 10; -- illegal
      B : Boolean := False;
   end record;

   -- See bodies for more cases.

   procedure Op1 (A : in out Integer;
                  B : in     Integer)
     with Depends => (A => (A, B));

   function Op2 (S : in String) return Positive;

   procedure Op3 (A : in out Integer;
                  B : in     Integer)
     with Depends => (A => (A, B));

end P;
