-- If_Airspeed test interface
--
-- $Log: if_airspeed-command.adb,v $
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
-- Revision 1.2  2003/09/10 20:07:49  adi
-- Added IBIT accessors
--
-- Revision 1.1  2003/08/10 16:56:28  adi
-- Initial revision
--
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking;
with Ibit.Io,Ibit.Checks;
with Measuretypes.Checks,Measuretypes.Io;
separate(If_Airspeed)
procedure Command is
   type Action is (Init,Check,Start_Ibit,Stop_ibit);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Speed,Ibit_phase);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Speed,Actual_speed : Measuretypes.Meter_Per_Sec;
      Exp_Valid,Actual_Valid : Boolean;
      Exp_Phase, Actual_Phase : Ibit.Phase;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Ibit_Phase =>
            Ibit.Io.Phase_Io.Get(Exp_Phase);
            Actual_Phase := Get_Ibit_State;
            Ibit.Checks.Phase(S => "If_Airspeed IBIT state",
                              Expected => Exp_Phase,
                              Actual   => Actual_Phase);
         when Speed =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            Measuretypes.Io.Speed_Io.Get(Exp_Speed);
            Get_Speed(Speed => Actual_Speed,
                       Valid => Actual_valid);
            Test.Checking.Bool(S => "If_Airspeed speed valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Measuretypes.Checks.Meter_Per_sec(S => "If_Airspeed speed",
                                    Expected => Exp_Speed,
                                    Actual => Actual_Speed);
            end if;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Airspeed Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("If_Airspeed Check ");
         Check;
      when Start_Ibit =>
         Ada.Text_Io.Put_Line("If_Airspeed IBIT Start");
         Ibit_Start;
      when Stop_Ibit =>
         Ada.Text_Io.Put_Line("If_Airspeed IBIT Stop");
         Ibit_Stop;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Airspeed.Command");
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Airspeed.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Airspeed.Command");

end Command;
