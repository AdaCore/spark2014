-- Sensor history type package
--
-- $Log: sensor_history.ads,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.5  2003/09/13 16:09:30  adi
-- Added rep clauses for types
--
-- Revision 1.4  2003/09/13 15:58:07  adi
-- Added individual types for distance, speed and angle
--
-- Revision 1.3  2003/09/07 18:49:17  adi
-- Made type private
--
-- Revision 1.2  2003/09/07 18:43:06  adi
-- Added reading functions
--
-- Revision 1.1  2003/09/07 18:28:19  adi
-- Initial revision
--
-- Revision 1.1  2003/09/01 19:50:09  adi
-- Initial revision
--
--

with
  measuretypes,
  Clock;
--# inherit measuretypes,
--#   clock;
package Sensor_history
is
   -- Type size is ceil(log_2(400_000)) = 19 bits
   subtype Meter is Measuretypes.Meter;

   -- Type size is ceil(log_2(360)) = 9 bits
   subtype Angle_Degrees is Measuretypes.Angle_Degrees;
   -- Type size is ceil(log_2(10_000)) = 14 bits
   subtype Meter_Per_Sec is Measuretypes.Meter_Per_Sec;

   -- Type size is 2 bits
   type History_Count is range 1..4;
   --# assert history_count'base is integer;

   -- Type size is 4 x 24 bits = 96 bits
   type Time_List is array(History_Count) of Clock.Millisecond;
   pragma Pack(Time_List);
   for Time_List'Size use 96;

   Blank_Time_List : constant Time_List
     := Time_List'(others => 0);

   -- Type size is 4 x 19 = 72 bits, packing min is 80
   type Dist_History_list is array(History_Count)
     of Measuretypes.Meter;
   pragma Pack(Dist_History_List);
   for Dist_History_List'Size use 80;

   Blank_dist_list : constant Dist_History_list
     := Dist_History_list'(others => 0);

   -- Type size is 80 + 96 + 2 bits = 170 bits <= 22 bytes
   type Dist_History is record
      distance : Dist_History_List;
      Times    : Time_List;
      new_Idx  : History_Count;
   end record;
   for Dist_History'Alignment use 1;
   for Dist_History use record
      Distance at  0 range 0..79;
      Times    at 10 range 0..95;
      New_Idx  at 22 range 0..1;
   end record;
   for Dist_History'Size use 178;

   -- Type size is 4 x 9 = 36 bits
   type Angle_History_List is array(History_Count) of Angle_Degrees;
   pragma Pack(Angle_History_List);
   for Angle_History_List'Size use 36;

   Blank_Angle_List : constant Angle_History_List
     := Angle_History_List'(others => 0);

   -- Type size is 36 + 96 + 2 bits = 134 bits
   type Angle_History is record
      Bearing : Angle_History_List;
      Times   : Time_List;
      New_Idx : History_Count;
   end record;
   for Angle_History'Alignment use 1;
   for Angle_History use record
      Bearing at  0 range 0..35;
      Times   at  5 range 0..95;
      New_Idx at 17 range 0..1;
   end record;
   for Angle_History'Size use 138;

   -- Type size is 4 x 14 = 56 bits
   type speed_List is array(History_Count) of Meter_Per_Sec;
   pragma Pack(Speed_List);
   for Speed_List'Size use 56;

   Blank_speed_List : constant speed_List :=
     speed_List'(others => 0);

   -- Type size is 56 + 96 + 2 bits = 154 bits
   type Speed_History is record
      Speed : Speed_List;
      Times : Time_List;
      New_Idx : History_Count;
   end record;
   for Speed_History'Alignment use 1;
   for Speed_History use record
      Speed   at  0 range 0..55;
      Times   at  7 range 0..95;
      New_Idx at 19 range 0..1;
   end record;
   for Speed_History'Size use 154;

   type measure_History is private;

   Blank_History : constant Measure_History;

   function Next_Item(H : History_Count)
                     return History_Count;

   function Previous_Item(H : History_Count)
                         return History_Count;

   -- Accessor functions for the history trackers
   procedure Get_Recent_Meter(Item      : in Measure_History;
                              Recent    : out Meter;
                              Timestamp : out Clock.Millisecond);
   --# derives recent, timestamp from item;

   procedure Update_Meter_Reading(item : in out measure_History;
                                  Data : in Meter);
     --# global in out clock.time;
     --# derives item from *, Data, clock.time &
     --#         clock.time from *;


   procedure Update_Angle_Reading(item : in out Measure_History;
                                  Data : in     Angle_Degrees);
     --# global in out clock.time;
     --# derives item from *, Data, clock.time &
     --#         clock.time from *;

   procedure Get_Recent_angle(Item      : in Measure_History;
                              Recent    : out Angle_Degrees;
                              Timestamp : out Clock.Millisecond);
   --# derives recent, timestamp from item;


   procedure Update_Speed_Reading(item : in out measure_History;
                                  Data : in Meter_Per_sec);
     --# global in out clock.time;
     --# derives item from *, Data, clock.time &
     --#         clock.time from *;

   procedure Get_Recent_Speed(Item      : in Measure_History;
                              Recent    : out Meter_Per_sec;
                              Timestamp : out Clock.Millisecond);
   --# derives recent, timestamp from item;

private

   type Measure_History is record
      -- One or more of the following will be entered:
      distance : Dist_History_List;
      Bearing  : Angle_History_List;
      Speed    : Speed_List;
      -- And these are always used
      Times    : Time_List;
      new_Idx  : History_Count;
   end record;

   Blank_History : constant Measure_history
     := Measure_History'(distance => Blank_dist_List,
                         Bearing  => Blank_Angle_List,
                         Speed    => Blank_Speed_List,
                         Times    => Blank_Time_List,
                         New_Idx  => History_Count'First);
end Sensor_history;
