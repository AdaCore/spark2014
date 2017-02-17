with Renamed;

package body Report is

   procedure Result is
      X : Boolean;
   begin
      X := Renamed (False);
      pragma Assert (X);

      X := Renamed (True);
      pragma Assert (not X);
   end Result;

end Report;
