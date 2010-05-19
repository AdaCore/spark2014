-- Barometer test i/f
--
-- $Log: barometer-command.adb,v $
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
-- Revision 1.2  2003/09/10 20:02:26  adi
-- Added IBIT checks
--
-- Revision 1.1  2003/02/19 19:04:15  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.checking;
with Measuretypes.Checks,Measuretypes.Io;
separate(Barometer)
procedure Command is
   type Action is (Init,Check,Set,Fail_Next_ibit);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Altitude);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Height,Actual_height : Measuretypes.Meter;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Altitude =>
            Measuretypes.Io.Meter_Io.Get(Exp_Height);
            Read_Altitude(Actual_Height);
            Measuretypes.Checks.Meter(S => "Barometer altitude",
                                       Expected => Exp_Height,
                                       Actual => Actual_Height);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      Height : MeasureTypes.Meter;
      Vel : Measuretypes.Meter_Per_Sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Altitude =>
            Measuretypes.Io.Meter_Io.Get(Height);
            Measuretypes.Io.Speed_Io.Get(Vel);
            Set_Altitude_Profile(Height => Height,
                                  Dz => Vel);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("Barometer Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("Barometer Check ");
         Check;
      when Set =>
        Ada.Text_Io.Put("Barometer Set ");
        Set;
      when Fail_Next_Ibit =>
         Ada.Text_Io.Put_Line("Barometer Fail next Ibit");
         Fail_Next_Bit;
   end case;
   Ada.Text_Io.Skip_Line;
end Command;
