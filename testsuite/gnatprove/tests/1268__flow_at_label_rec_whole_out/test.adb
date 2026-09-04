pragma Extensions_Allowed (All_Extensions);

package body Test
with SPARK_Mode
is
   procedure Run
     (A1, A2 : Integer;
      X1, X2, Y1, Y2 : Boolean;
      O      : out RR)
   is
      Obj : RR := (A => A1, B => (X => X1, Y => Y1), C => (null record));
   begin
      <<Init>>
      Obj.A := A2;
      Obj.B.X := X2;
      Obj.B.Y := Y2;

      O := Obj'At (Init);
   end Run;
end Test;
