pragma Extensions_Allowed (All_Extensions);

package body Test
with SPARK_Mode
is
   function Capture
     (A1, A2 : Integer;
      X1, X2 : Boolean) return Rec
   is
      Obj : Rec := (A => A1, X => X1);
   begin
      <<Init>>
      Obj.A := A2;
      Obj.X := X2;

      return Obj'At (Init);
   end Capture;
end Test;
