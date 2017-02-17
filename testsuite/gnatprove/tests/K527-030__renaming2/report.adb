with Renamed;

package body Report is

   procedure Result is
      X : Boolean;
   begin
      X := Renamed.Opposite (False);
      pragma Assert (X);

      X := Renamed.Opposite (True);
      pragma Assert (not X);
   end Result;

end Report;
