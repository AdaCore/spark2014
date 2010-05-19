-- Drag testing
-- $Log: drag-testpoint.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/12 18:13:41  adi
-- Initial revision
--
--
with ada.text_io;
separate(drag)
procedure testpoint is
   package speed_io is new ada.text_io.integer_io(measuretypes.meter_per_sec);
   package accel_io is new ada.text_io.integer_io(measuretypes.cm_per_sec_2);
   package force_io is new ada.text_io.integer_io(measuretypes.newton);
   speed : pos_meter_per_sec;
   altitude : pos_meter;
   drag_force : measuretypes.newton;
begin
   ada.text_io.put_Line("Drag:");
   ada.text_io.put_Line("  Altitude =      0   5,000  10,000  15,000  m");
   for j in integer range 0..15 loop
      speed := pos_meter_per_sec(j * 50);
      speed_io.put(item => speed, width => 4);
      ada.text_io.put("m/s => ");
      for I in integer range 0..3 loop
         altitude := pos_meter(i * 5_000);
         calc_drag(profile => 100,
                   speed => speed,
                   altitude => altitude,
                   drag_force => drag_force);
         force_io.put(item => drag_force, width => 8);
      end loop;
      ada.text_io.put_line(" N");
   end loop;
exception
  when Constraint_Error =>
      ada.text_io.put_line("Constraint_Error in Test_Aux");
   when others =>
      ada.text_io.put_line("Unknown exception in Test_Aux");
end testpoint;
