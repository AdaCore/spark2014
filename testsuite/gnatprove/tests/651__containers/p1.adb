with P2;
package body P1 with SPARK_Mode is
   procedure Lemma is
      V : C;
      B : Boolean;
   begin
      V := Add (V, -1);
      B := P2.My_True (V);
   end Lemma;

end P1;
