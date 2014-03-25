package body Logic
is

   function Ok (V: in Integer) return Boolean
     with Convention => Ghost,
          Import;

   pragma Warnings (Off, "* has no effect");
   procedure Implies_Test
     with Depends => null
   is
   begin
      pragma Assert ((if False then False));
      pragma Assert ((if False then True));
      pragma Assert (not (if True then False));
      pragma Assert ((if True then True));

      --  We will need the extra asserts to avoid introducing false facts.

      pragma Assert (not (if False then False));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (if False then True));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert ((if True then False));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (if True then True));  --  @ASSERT:FAIL

      null;
   end Implies_Test;

   pragma Warnings (Off, "* has no effect");
   procedure Equivalence_Test
     with Depends => null
   is
   begin
      pragma Assert (False = False);  --  @ASSERT:PASS
      pragma Assert (not (False = True));  --  @ASSERT:PASS
      pragma Assert (not (True = False));  --  @ASSERT:PASS
      pragma Assert (True = True);  --  @ASSERT:PASS

      --  We will need the extra asserts to avoid introducing false facts.

      pragma Assert (not (False = False));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (False = True);  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (True = False);  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (True = True));  --  @ASSERT:FAIL
      null;
   end Equivalence_Test;
   pragma Warnings (On, "* has no effect");

   pragma Warnings (Off, "* has no effect");
   procedure De_Morgan
      with Depends => null
   is
      A, B : Boolean;
   begin

      A := False;
      B := False;
      pragma Assert_And_Cut (True);
      pragma Assert (not (A or B) = (not A and not B));  --  @ASSERT:PASS

      pragma Assert_And_Cut (True);
      pragma Assert ((not (A and B)) = (not A or not B));  --  @ASSERT:PASS

      --  And now for some false ones...

      pragma Assert_And_Cut (True);
      pragma Assert ((not (A and B)) = (not A and not B));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert ((A or B) = (not A and not B));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (A or B) = (A and not B));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (A or B) = (not A and B));  --  @ASSERT:FAIL
   end De_Morgan;
   pragma Warnings (On, "* has no effect");

   procedure Contraposition
     with Depends => null
   is
      A, B : Boolean;
   begin
      A := False;
      B := False;

      pragma Assert_And_Cut (True);
      pragma Assert (if (if not A then not B) then (if B then A));  --  @ASSERT:PASS
   end Contraposition;

   function XOR_Test_A (A, B: Boolean) return Boolean
     with Post => XOR_Test_A'Result = A xor B  --  @ASSERT:PASS
   is
      R : Boolean;
   begin
      if A and B then
         R := False;
      elsif not A and not B then
         R := False;
      elsif A and not B then
         R := True;
      else
         R := True;
      end if;
      return R;
   end XOR_Test_A;

   procedure XOR_Test_B
     with Depends => null
   is
      A, B : Boolean;
   begin
      A := False;
      B := False;

      pragma Assert_And_Cut (True);
      pragma Assert ((A xor B) = ((A or B) and (not (A and B))));  --  @ASSERT:PASS

      pragma Assert_And_Cut (True);
      pragma Assert ((A xor B) = ((A and not B) or (not A and B)));  --  @ASSERT:PASS
   end XOR_Test_B;

   pragma Warnings (Off, "* has no effect");
   procedure Equivalence_Test_2 (A: in Integer)
     with Depends => (null => A),
          Pre     => (A > 0) = Ok (A),
          Post    => Ok (A) = (A > 0)
   is
   begin
      null;
   end Equivalence_Test_2;
   pragma Warnings (On, "* has no effect");

   function Equivalence_Test_3 (A, B, C: in Boolean) return Boolean
     with Post => Equivalence_Test_3'Result = ((A = B) = C)
   is
   begin
      return A = (B = C);
   end Equivalence_Test_3;

   --  Implication is not associative.
   function Implies_Test_1 (A, B, C: in Boolean) return Boolean
     with Depends => (Implies_Test_1'Result => null,
                      null => (A, B, C)),
          Post    => Implies_Test_1'Result =  --  @POSTCONDITION:FAIL
            ((if (if A then B) then C) = (if A then (if B then C)))
   is
   begin
      return True;
   end Implies_Test_1;

end Logic;
