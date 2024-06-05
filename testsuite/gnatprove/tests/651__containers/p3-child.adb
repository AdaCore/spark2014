with P2;
package body P3.Child with SPARK_Mode is
   procedure Lemma is
      V : C;
      B : Boolean;
   begin
      V := Add (V, -1); --  @INVARIANT_CHECK:FAIL
      B := P2.My_True (V);
   end Lemma;

end P3.Child;
