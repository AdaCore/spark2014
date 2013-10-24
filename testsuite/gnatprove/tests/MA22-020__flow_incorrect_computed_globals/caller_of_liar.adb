with Hidden_Liar; use Hidden_Liar;

package body Caller_Of_Liar
  with SPARK_Mode
is
   procedure Add_Three (X, Y, Z : in     Integer;
                        T       :    out Integer)
   is
      Tmp, Tmp2 : Integer;
   begin
     Add (X, Y, Tmp);
     Add (Tmp, Z, Tmp2);
     T := Tmp2;
   end Add_Three;
end Caller_Of_Liar;

