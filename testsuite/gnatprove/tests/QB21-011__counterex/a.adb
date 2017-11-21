package body A with SPARK_Mode is

   procedure Add (A : in out Integer;
                  B : Integer)
   is
   begin
      A := A + 1;
      pragma Assert (A + B = 2); -- @FAIL @COUNTEREXAMPLES
   end Add;

   procedure Add1 (A : in out Integer;
                   B : Integer)
   is
   begin
      A := A + 1;
      pragma Assert (A + B = 2); -- @FAIL @COUNTEREXAMPLES
   end Add1;

end A;
