-- Airspeed test interface
-- Ada, not SPARK
--
-- $Log: airspeed-command.adb,v $
-- Revision 1.3  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/10 20:01:22  adi
-- Added IBIT checks
--
-- Revision 1.1  2003/08/09 09:35:31  adi
-- Initial revision
--
--
--
with Ada.Text_Io;
with Test_Keywords,Test.checking;
with Measuretypes.Checks,Measuretypes.Io;
separate(Airspeed)
procedure Command is
   type Action is (Init,Check,Set,Fail_Next_ibit);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Speed);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_speed,Actual_speed : Measuretypes.Meter_Per_sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Speed =>
            Measuretypes.Io.Speed_Io.Get(Exp_Speed);
            Read_Airspeed(Actual_Speed);
            Measuretypes.Checks.Meter_Per_Sec(S => "Airspeed ",
                                              Expected => Exp_Speed,
                                              Actual => Actual_Speed);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      New_Speed : MeasureTypes.Meter_Per_sec;
      accel : Measuretypes.cm_Per_Sec_2;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Speed =>
            Measuretypes.Io.Speed_Io.Get(New_Speed);
            Measuretypes.Io.Accel_Cm_Io.Get(accel);
            Set_Airspeed_Profile(Speed => New_Speed,
                                 Accel => Accel);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("Airspeed Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("Airspeed Check ");
         Check;
      when Fail_Next_Ibit =>
         Ada.Text_Io.Put_Line("Airspeed Fail next Ibit");
         Fail_Next_Bit;
      when Set =>
        Ada.Text_Io.Put("Airspeed Set ");
        Set;
   end case;
   Ada.Text_Io.Skip_Line;
end Command;
