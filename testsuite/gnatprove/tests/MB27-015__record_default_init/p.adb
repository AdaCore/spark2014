with FSNB;

package body P
  with SPARK_Mode => On
is
   BC1 : constant Integer := 1;
   BC2 : constant Integer := 2;

   type RB1 is record
      --  Expressions involving FSB.F1 which is a pure
      --  function with no globals, although its has NO Global
      --  contract
      F1 : Integer := FSB.F1 (1, 2);     -- Legal - literal args
      F2 : Integer := FSB.F1 (BC1, BC2); -- Legal - constant args
      F3 : Integer := FSB.F1 (1, FSB.S); -- Illegal - FSB.S is a var

      --  Expressions involving FSB.F2 which is a pure
      --  function that DOES reference a variable in its
      --  body, but it has no Global contract
      F4 : Integer := FSB.F2 (1, 2);     -- Illegal - refs FSB.S
      F5 : Integer := FSB.F2 (BC1, BC2); -- Illegal - refs FSB.S
      F6 : Integer := FSB.F2 (1, FSB.S); -- Illegal - refs FSB.S

      --  Expressions involving FSB.F3 which is a pure
      --  function with no globals stated in its Global contract
      F7 : Integer := FSB.F3 (1, 2);     -- Legal - literal args
      F8 : Integer := FSB.F3 (BC1, BC2); -- Legal - constant args
      F9 : Integer := FSB.F3 (1, FSB.S); -- Illegal - S is a var

      --  Expressions involving FSB.F4 which is a pure
      --  function that DOES reference a variable in its
      --  body AND has a correct Global contract
      F10 : Integer := FSB.F4 (1, 2);     -- Illegal - refs FSB.S
      F11 : Integer := FSB.F4 (BC1, BC2); -- Illegal - refs FSB.S
      F12 : Integer := FSB.F4 (1, FSB.S); -- Illegal - refs FSB.S

   end record;


   type RB2 is record
      --  Expressions involving FSNB.F5 which is a function
      --  with unknown globals and no body
      F1 : Integer := FSNB.F5 (1, 2);      -- Legal
      F2 : Integer := FSNB.F5 (BC1, BC2);  -- Legal
      F3 : Integer := FSNB.F5 (1, FSNB.S); -- Illegal - FSNB.S is a var

      --  Expressions involving FSNB.F6 which is a function
      --  with an explicity Global => null, but no body
      F4 : Integer := FSNB.F6 (1, 2);      -- Legal
      F5 : Integer := FSNB.F6 (BC1, BC2);  -- Legal
      F6 : Integer := FSNB.F6 (1, FSNB.S); -- Illegal - FSNB.S is a var

      --  Expressions involving FSNB.F7 which is a
      --  function with an explicit Global contract and DOES
      --  reference a variable
      F7 : Integer := FSNB.F7 (1, 2);      -- Illegal - FSNB.S is a var
      F8 : Integer := FSNB.F7 (BC1, BC2);  -- Illegal - FSNB.S is a var
      F9 : Integer := FSNB.F7 (1, FSNB.S); -- Illegal - FSNB.S is a var
   end record;



   procedure Op1 (A : in out Integer;
                  B : in     Integer)
   is
      C1 : constant Integer := 1; -- literal constant

      C2 : constant Integer := B; -- constant depends on "in" param

      -- Default initialization depends on an "in" parameter.  Legal
      -- since "in" params are constants
      type R4 is record
         F1 : Integer := B;
      end record;

      -- Default initialization depends on constant C1. Legal
      type R5 is record
         F1 : Integer := C1;
      end record;

      -- Default initialization depends on constant C2. Legal
      type R6 is record
         F1 : Integer := C2;
      end record;

      -- Default initialization depends on constants C1 and C2. Legal
      type R7 is record
         F1 : Integer := C1 + C2;
      end record;
   begin
      A := A + B;
   end Op1;

   function Op2 (S : in String) return Positive
   is
      type R is record
         F1 : Positive := S'Last; -- Legal
      end record;
      X : R;
   begin
      --  Interesting test of the flow analyser too.
      --  The value (content) of S is not used, but S'Last is used.
      --  Should this be reported as an error?
      return X.F1;
   end Op2;


   --  Shows legality of a "for" loop parameter used as a default initial
   --  value in a record type component declaration.  Ada LRM says that
   --  a loop parameter is viewed as "constant" (Ada LRM 3.3(18))
   procedure Op3 (A : in out Integer;
                  B : in     Integer)
   is
   begin
      for I in Integer range 1 .. B loop
         declare
            type R is record
               F1 : Integer := I; -- legal
               F2 : Integer := 0; -- legal
               F3 : Integer := I + 1; -- legal
            end record;
            Q : R;
         begin
            A := A + Q.F1;
         end;
      end loop;
   end Op3;

end P;
