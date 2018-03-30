with Spacecraft; use Spacecraft;

--pragma SPARK_Mode On;

package Known_Satellites
with
  SPARK_Mode => On,
  Abstract_State => (Known_Satellite_Count_State, Known_Satellite_List_State),
  Initializes => (Known_Satellite_Count_State, Known_Satellite_List_State),
  Initial_Condition => (Get_Satellite_Count = 0)
is

   Max_Satellites : constant := 10; -- arbitrary
   type Satellite_Count is range 0 .. Max_Satellites;

   type Satellite_Reference is limited private;
   
   function Get_Satellite_Count return Satellite_Count;
   --function Full return Boolean;
   function Is_Satellite_Reference_Valid(Reference:  Satellite_Reference) return Boolean;

   --  Insert the satellite Value into the repository of known satellites.
   --  The output Reference provides a reference to that satellite within the
   --  repository and can be used as such in other routines to retrieve and/or
   --  alter the corresponding satellite value.
   --pragma Unevaluated_Use_Of_Old (Warn);
   pragma Unevaluated_Use_Of_Old (Allow);
   procedure Insert_Satellite
     (Value     : in     Satellite;
      Reference :    out Satellite_Reference)
     with
       Global  => (In_Out => (Known_Satellite_Count_State, Known_Satellite_List_State)),
       Depends => (Reference => (Known_Satellite_Count_State),
                  Known_Satellite_Count_State => Known_Satellite_Count_State,
                  Known_Satellite_List_State =>+ (Value, Known_Satellite_Count_State)),
       Pre     => (Get_Satellite_Count < Satellite_Count'Last),
       --Pre    => (not Full),
       Post    => ( (Is_Satellite_Reference_Valid(Reference)) and then 
                     (Get_Satellite_Count = Get_Satellite_Count'Old + 1) );
     --and then
     --              (Reference = Get_Satellite_Count) );

   --  Update the satellite designated in the repository by Reference with the
   --  new Value.
   procedure Update_Satellite
     (Value     : in Satellite;
      Reference : in Satellite_Reference)
     with
       Global  => (In_Out => Known_Satellite_List_State),
       Depends => (Known_Satellite_List_State =>+ (Value, Reference)),
       Pre     => (Is_Satellite_Reference_Valid(Reference));

   --  Get a copy of the Value of the satellite designated by Reference. The
   --  repository is not changed.
   procedure Get_Satellite
     (Reference : in     Satellite_Reference;
      Value     :    out Satellite)
     with
       Global  => (Input => Known_Satellite_List_State),
       Depends => (Value => (Known_Satellite_List_State, Reference)),
       Pre     => (Is_Satellite_Reference_Valid(Reference));

   --  A convenience routine that returns a copy of the satellite value
   --  designated by Reference. The repository is not changed.
   function Dereferenced (Reference : Satellite_Reference) return Satellite
     with
       Global  => (Input => Known_Satellite_List_State),
       Depends => (Dereferenced'Result => (Known_Satellite_List_State, Reference)),
       Pre   => (Is_Satellite_Reference_Valid(Reference));

private

   type Satellite_Reference is range Satellite_Count'First .. Satellite_Count'Last with
     Default_Value => 0;

   currSatelliteCount: Satellite_Count := 0 with Part_Of => Known_Satellite_Count_State;
   function Get_Satellite_Count return Satellite_Count is (currSatelliteCount);
   --function Full return Boolean is (currSatelliteCount = Satellite_Count'Last);
   
end Known_Satellites;
