-- Nav i/f
--
-- $Log: nav-command.adb,v $
-- Revision 1.3  2004/12/17 17:51:22  adi
-- Fixed compass angle conversions and checks so that compass.in passes
--
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/07 20:25:49  adi
-- Initial revision
--
--
with Ada.Text_Io,Measuretypes.Io,Measuretypes.checks;
with Test_Keywords,Test.Checking,Measuretypes.Angle_ops;
separate(nav)
procedure Command is
   type Action is (Check);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Nav ";

   type Measurement is (Height,Offset,Heading,Speed);
   package Measurement_Io is new Ada.Text_Io.Enumeration_Io(Measurement);

   package Confidence_Io is new Ada.Text_Io.Enumeration_Io(Confidence);

   procedure Check is
      This_Measure : Measurement;
      Exp_Confid, Actual_Confid : Confidence;
      Exp_Meter, Actual_Meter : Meter;
      Exp_Angle, Actual_Angle : Angle_Degrees;
      Exp_Speed, Actual_Speed : Meter_Per_sec;
   begin
      Measurement_Io.Get(This_measure);
      Ada.Text_Io.Put_Line(Measurement'Image(This_measure));
      case This_measure is
         when Height =>
            Measuretypes.Io.Meter_Io.Get(Exp_Meter);
            Confidence_Io.Get(Exp_Confid);
            Estimate_Height(M => Actual_Meter,
                            C => Actual_Confid);
            Measuretypes.Checks.Meter(S => Entity,
                                      Expected => Exp_Meter,
                                      Actual => Actual_Meter);
            Test.Checking.Bool(S => Entity & " confidence",
                               Expected => True,
                               Actual => (Exp_Confid = Actual_Confid));
         when Offset =>
            Measuretypes.Io.Meter_Io.Get(Exp_Meter);
            Confidence_Io.Get(Exp_Confid);
            Estimate_Origin_offset(M => Actual_Meter,
                                   C => Actual_Confid);
            Measuretypes.Checks.Meter(S => Entity,
                                      Expected => Exp_Meter,
                                      Actual => Actual_Meter);
            Test.Checking.Bool(S => Entity & " confidence",
                               Expected => True,
                               Actual => (Exp_Confid = Actual_Confid));
         when Heading =>
            Measuretypes.Io.angle_Io.Get(Exp_angle);
            Confidence_Io.Get(Exp_Confid);
            Estimate_heading(A => Actual_angle,
                             C => Actual_Confid);
            Measuretypes.Checks.Angle_Degrees(S => Entity,
                                              Expected => Exp_angle,
                                              Actual => Actual_angle);
            Test.Checking.Bool(S => Entity & " confidence",
                               Expected => True,
                               Actual => (Exp_Confid = Actual_Confid));
         when Speed =>
            Measuretypes.Io.Speed_Io.Get(Exp_speed);
            Confidence_Io.Get(Exp_Confid);
            Estimate_speed(s => Actual_speed,
                             C => Actual_Confid);
            Measuretypes.Checks.Meter_Per_sec(S => Entity,
                                              Expected => Exp_speed,
                                              Actual => Actual_speed);
            Test.Checking.Bool(S => Entity & " confidence",
                               Expected => True,
                               Actual => (Exp_Confid = Actual_Confid));
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Check =>
         Ada.Text_Io.Put(Entity & "Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in Nav.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in Nav.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in Nav.Command");

end Command;
