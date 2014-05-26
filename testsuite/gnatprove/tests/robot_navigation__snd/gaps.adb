
package body Gaps is

   function Create return Gap is
   begin
      return (bearing => Spaces.Angles.Create (0.0), distance => 0.0, iDir => 0);
   end Create;

   function Create (ang : Angle; d : Float; iD : iDir_t) return Gap is
   begin
      return (bearing => ang, distance => d, iDir => iD);
   end Create;

   function Equal (Left, Right : Gap) return Boolean is
   begin
      return
        Left.bearing = Right.bearing and then
        Left.distance = Right.distance and then
        Left.iDir = Right.iDir;
   end Equal;

end Gaps;
