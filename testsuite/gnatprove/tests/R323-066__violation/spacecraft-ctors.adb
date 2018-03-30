pragma Ada_2012;
package body Spacecraft.Ctors
  with SPARK_Mode => On
is

   --     function New_Satellite
   --       (Time: DKFloat;
   --        Revolutions: DKFloat;
   --        Altitude: DKFloat)
   --        return Satellite
   --     is
   --     begin
   --        --  Generated stub: replace with real body!
   --        pragma Compile_Time_Warning (Standard.True, "New_Satellite unimplemented");
   --        return raise Program_Error with "Unimplemented function New_Satellite";
   --     end New_Satellite;

   function New_Satellite(Time: DKTime; Revolutions: DKFloat; Altitude: DKFloat) return Satellite is
     (Time        => Time,
      Revolutions => Revolutions,
      Altitude    => Altitude);

end Spacecraft.Ctors;
