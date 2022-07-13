package body Logic
is

   function Ok (V: in Integer) return Boolean
     with Ghost,
          Import,
          Global   => null,
          Annotate => (GNATprove, Always_Return);

   pragma Warnings (Off, "unused initial value of *");
   pragma Warnings (Off, "subprogram * has no effect");

   procedure Implies_Test (T : Boolean;
                           F : Boolean)
     with Pre => T and not F
   is
   begin
      pragma Assert ((if F then F));      --  @ASSERT:PASS
      pragma Assert ((if F then T));      --  @ASSERT:PASS
      pragma Assert (not (if T then F));  --  @ASSERT:PASS
      pragma Assert ((if T then T));      --  @ASSERT:PASS

      --  We will need the extra asserts to avoid introducing false facts.

      pragma Assert (not (if F then F));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (if F then T));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert ((if T then F));      --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (if T then T));  --  @ASSERT:FAIL

      null;
   end Implies_Test;

   procedure Equivalence_Test (T : Boolean;
                               F : Boolean)
     with Pre => T and not F
   is
   begin
      pragma Assert (F = F);        --  @ASSERT:PASS
      pragma Assert (not (F = T));  --  @ASSERT:PASS
      pragma Assert (not (T = F));  --  @ASSERT:PASS
      pragma Assert (T = T);        --  @ASSERT:PASS

      --  We will need the extra asserts to avoid introducing false facts.

      pragma Assert_And_Cut (True);
      pragma Assert (F = T);        --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (T = F);        --  @ASSERT:FAIL

      null;
   end Equivalence_Test;

   procedure De_Morgan (A, B : Boolean)
   is
   begin
      pragma Assert_And_Cut (True);
      pragma Assert (not (A or B) = (not A and not B));     --  @ASSERT:PASS

      pragma Assert_And_Cut (True);
      pragma Assert ((not (A and B)) = (not A or not B));   --  @ASSERT:PASS

      --  And now for some false ones...

      pragma Assert_And_Cut (True);
      pragma Assert ((not (A and B)) = (not A and not B));  --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert ((A or B) = (not A and not B));         --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (A or B) = (A and not B));         --  @ASSERT:FAIL

      pragma Assert_And_Cut (True);
      pragma Assert (not (A or B) = (not A and B));         --  @ASSERT:FAIL
   end De_Morgan;

   procedure Contraposition (A, B : Boolean)
   is
   begin
      pragma Assert_And_Cut (True);
      pragma Assert (if (if not A then not B)  --  @ASSERT:PASS
                     then (if B then A));
   end Contraposition;

   function XOR_Test_A (A, B: Boolean) return Boolean
     with Post => XOR_Test_A'Result = A xor B  --  @POSTCONDITION:PASS
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

   procedure XOR_Test_B (A, B: Boolean)
   is
   begin
      pragma Assert_And_Cut (True);
      pragma Assert ((A xor B) = ((A or B) and (not (A and B))));  --  @ASSERT:PASS

      pragma Assert_And_Cut (True);
      pragma Assert ((A xor B) = ((A and not B) or (not A and B)));  --  @ASSERT:PASS
   end XOR_Test_B;

   procedure Equivalence_Test_2 (A: in Integer)
     with Depends => (null => A),
          Pre     => (A > 0) = Ok (A),
          Post    => Ok (A) = (A > 0) --  @POSTCONDITION:PASS
   is
   begin
      null;
   end Equivalence_Test_2;

   function Equivalence_Test_3 (A, B, C: in Boolean) return Boolean
     with Post => Equivalence_Test_3'Result = ((A = B) = C)  --  @POSTCONDITION:PASS
   is
   begin
      return A = (B = C);
   end Equivalence_Test_3;

   --  Implication is not associative.
   procedure Implies_Test_1 (A, B, C: in Boolean)
   is
   begin
      pragma Assert ((if (if A then B) then C) =  --  @ASSERT:FAIL
                     (if A then (if B then C)));
   end Implies_Test_1;

end Logic;
