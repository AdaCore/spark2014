package P is
   type Color is (Red, Blue, Green);
   type Dots is array (Color) of Integer;

   type Repr is (A, B, C);
   for Repr use (A => 1, B => 5, C => 8);

   procedure Shadow_Effect (D : in out Dots) with
      --  should not be proved
     Post => (for all C in Color => False); -- @POSTCONDITION:FAIL

   function P (R : Repr) return Integer
      with Pre  => (R = C),
      --  should not be proved
           Post => (P'Result = 8); -- @POSTCONDITION:FAIL

   function Q (R : Repr) return Integer
      with Pre  => (R = C),
      --  should be proved
           Post => (Q'Result = 2); -- @POSTCONDITION:PASS
end P;
