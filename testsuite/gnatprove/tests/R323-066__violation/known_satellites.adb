with Spacecraft.Ctors; use Spacecraft.Ctors;

package body Known_Satellites
with
  SPARK_Mode => On,
  Refined_State => (Known_Satellite_Count_State => currSatelliteCount,
                    Known_Satellite_List_State => SatelliteArray)
is
   
   SatelliteArray: array (1..Satellite_Count'Last) of Satellite := (others => New_Satellite(1.0, 0.0, 0.0));

   function Is_Satellite_Reference_Valid(Reference:  Satellite_Reference) return Boolean is (Reference > Satellite_Reference'First);

   ------------------------
   --  Insert_Satellite  --
   ------------------------
   procedure Insert_Satellite
     (Value     : in     Satellite;
      Reference :    out Satellite_Reference)
   is
   begin
      currSatelliteCount := currSatelliteCount + 1;
      SatelliteArray(currSatelliteCount) := Value;
      Reference := Satellite_Reference(currSatelliteCount);
   end Insert_Satellite;

   ------------------------
   --  Update_Satellite  --
   ------------------------
   procedure Update_Satellite
     (Value     : in Satellite;
      Reference : in Satellite_Reference)
   is
   begin
      SatelliteArray(Satellite_Count(Reference)) := Value;
   end Update_Satellite;

   ---------------------
   --  Get_Satellite  --
   ---------------------
   procedure Get_Satellite
     (Reference : in     Satellite_Reference;
      Value     :    out Satellite)
   is
   begin
      Value := SatelliteArray(Satellite_Count(Reference));
   end Get_Satellite;

   --------------------
   --  Dereferenced  --
   --------------------
   function Dereferenced (Reference : Satellite_Reference) return Satellite is
      (SatelliteArray(Satellite_Count(Reference)));

end Known_Satellites;
