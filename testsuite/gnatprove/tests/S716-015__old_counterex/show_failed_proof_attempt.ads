package Show_Failed_Proof_Attempt with SPARK_Mode is

   C : Natural := 100;

   procedure Increase (X : in out Natural) with Post => (if X'Old < C then
                X > X'Old
              else X = C); -- @COUNTEREXAMPLE

   procedure Increase2 (X : in out Natural)
     with Post => (if X'Old < C then
                     X > X'Old
                   else X = C); -- @COUNTEREXAMPLE

   procedure Increase3 (X : in out Natural)

     with Post => (if X'Old < C then
                     X > X'Old
                   else X = C); -- @COUNTEREXAMPLE

   procedure Increase4 (X : in out Natural)
     with Post => (if X'Old < C then X > X'Old else X = C); -- @COUNTEREXAMPLE

end Show_Failed_Proof_Attempt;
