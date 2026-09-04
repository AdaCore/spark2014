pragma Extensions_Allowed (All_Extensions);

package Test
with SPARK_Mode
is
   type Rec is record
      A : Integer;
      X : Boolean;
   end record;

   function Capture
     (A1, A2 : Integer;
      X1, X2 : Boolean) return Rec
   with Depends => (Capture'Result => (A1, X1), null => (A2, X2));
end Test;
