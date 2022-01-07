with Ada.Text_IO;  use Ada.Text_IO;
--with Ada.Numerics; use Ada.Numerics;  -- for Pi
--with System;
with Spacecraft.Ctors; use Spacecraft; use Spacecraft.Ctors;
with Known_Satellites;use Known_Satellites;

pragma Warnings(Off, "no Global contract available for ""Put_Line""");

procedure Display_Velocities
  with
    SPARK_Mode => On--,
    --Pre => (Get_Satellite_Count = 0)
is
   -- TIP: pragma Discard_Names; -- Language defined pragma needed for falcon to discard strings from binary
   -- TIP: https://www.adacore.com/gems
   -- TIP: In Ada, array index is checked only when it is on LHS but you can turn it on even for RHS. SPARK always has this on.

   -- Question for adacore: How to ensure initialization goes into code section instead of data section
   -- Question for adacore: Does default component value go into code section or data section

   -- Question for adacore: Using Ctrl + Space didn't put "begin". Also, would like to
   -- get even "is" typed up and not have to type it the moment I hit Ctrl+Space
   -- after typing "procedure". Note that SlickEdit does this without any shortcut
   -- meaning just doing a space causes everything to automtically happen which is
   -- even nicer

   -- Question for adacore: How to do ct_assert

   type Country is (USA, RSA);


   procedure Display_Velocities_SPARK
     --with
     --Pre => (Get_Satellite_Count = 0)
   is

      --type SatelliteArr is array(Country) of Satellite;
      SatelliteTmp: Satellite;
      SatRefArray: array(Country) of Satellite_Reference;
   begin

      SatelliteTmp := New_Satellite(Time => 36_320.2 / 60.0, Revolutions => 10.0, Altitude => 22_256_384.2 / 5_280.0);
      --pragma Assert(Get_Satellite_Count = 0);
      Insert_Satellite(SatelliteTmp, SatRefArray(USA));
      --Put_Line("[SPK] Satellite Velocity for USA is " & DKFloat'Image(VelocityFun(Dereferenced(SatRefArray(USA)))) & " mph ");

      pragma Annotate(GNATprove, Intentional, "*range check*", "Some issue with Put_Line");
      Put_Line("[SPK] Satellite Velocity for USA is " & DKFloat'Image(Velocity(SatelliteTmp)) & " mph ");

      SatelliteTmp := New_Satellite(Time => 680.2,           Revolutions => 11.0, Altitude => 12_147.7 * 0.62137);
      Insert_Satellite(SatelliteTmp, SatRefArray(RSA));
      Put_Line("[SPK] Satellite Velocity for RSA is " & DKFloat'Image(Velocity(Dereferenced(SatRefArray(RSA)))) & " mph ");

   end Display_Velocities_SPARK;

begin
   --Display_Velocities_2D_Array;
   --Display_Velocities_Record;
   Display_Velocities_SPARK;
end Display_Velocities;
