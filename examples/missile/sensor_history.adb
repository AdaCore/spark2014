-- Sensor history type implementation
--
-- $Log: sensor_history.adb,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/07 18:44:19  adi
-- Initial revision
--

package body Sensor_history
is
   -- Modular history count
   function Next_Item(H : History_Count)
                     return History_Count
   is
      Ans : History_Count;
   begin
      if H = History_Count'Last then
         Ans := History_Count'First;
      else
         Ans := 1 + H;
      end if;
      return Ans;
   end Next_item;

   function previous_Item(H : History_Count)
                     return History_Count
   is
      Ans : History_Count;
   begin
      if H = History_Count'first then
         Ans := History_Count'last;
      else
         Ans := H - 1;
      end if;
      return Ans;
   end Previous_item;

   -- Accessor functions for the history trackers

   procedure Get_Recent_Meter(Item      : in Measure_History;
                              Recent    : out Meter;
                              Timestamp : out Clock.Millisecond)
   is
      Prev_Idx : History_Count;
   begin
      Prev_Idx := Previous_Item(Item.New_Idx);
      Recent := Item.Distance(Prev_Idx);
      Timestamp := Item.Times(Prev_Idx);
   end Get_Recent_Meter;

   procedure Update_Meter_Reading(item : in out measure_History;
                                  Data : in Meter)
   is
      T : Clock.Millisecond;
      T_Valid : Boolean;
   begin
      Clock.Read(T => T,
                 Valid => T_Valid);
      if T_Valid then
         Item.Times(Item.New_Idx) := T;
      else
         Item.Times(Item.New_Idx) := 0;
      end if;
      item.Distance(item.New_Idx) := Data;
      Item.New_Idx := Next_Item(Item.New_Idx);
   end Update_Meter_Reading;


   procedure Get_Recent_angle(Item      : in     Measure_History;
                              Recent    :    out Angle_Degrees;
                              Timestamp :    out Clock.Millisecond)
   is
      Prev_Idx : History_Count;
   begin
      Prev_Idx := Previous_Item(Item.New_Idx);
      Recent := Item.bearing(Prev_Idx);
      Timestamp := Item.Times(Prev_Idx);
   end Get_Recent_angle;

   procedure Update_angle_Reading(item : in out Measure_History;
                                  Data : in     Angle_Degrees)
   is
      T : Clock.Millisecond;
      T_Valid : Boolean;
   begin
      Clock.Read(T => T,
                 Valid => T_Valid);
      if T_Valid then
         Item.Times(Item.New_Idx) := T;
      else
         Item.Times(Item.New_Idx) := 0;
      end if;
      item.bearing(item.New_Idx) := Data;
      Item.New_Idx := Next_Item(Item.New_Idx);
   end Update_angle_Reading;


   procedure Get_Recent_speed(Item      : in Measure_History;
                              Recent    : out Meter_Per_sec;
                              Timestamp : out Clock.Millisecond)
   is
      Prev_Idx : History_Count;
   begin
      Prev_Idx := Previous_Item(Item.New_Idx);
      Recent := Item.speed(Prev_Idx);
      Timestamp := Item.Times(Prev_Idx);
   end Get_Recent_speed;

   procedure Update_Speed_Reading(item : in out measure_History;
                                  Data : in Meter_Per_sec)
   is
      T : Clock.Millisecond;
      T_Valid : Boolean;
   begin
      Clock.Read(T => T,
                 Valid => T_Valid);
      if T_Valid then
         Item.Times(Item.New_Idx) := T;
      else
         Item.Times(Item.New_Idx) := 0;
      end if;
      item.speed(item.New_Idx) := Data;
      Item.New_Idx := Next_Item(Item.New_Idx);
   end Update_Speed_Reading;

end Sensor_history;

