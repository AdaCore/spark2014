-- If_Barometer test i/f
--
-- $Log: if_barometer-command.adb,v $
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
-- Revision 1.2  2003/09/10 20:09:48  adi
-- Added IBIT accessor
--
-- Revision 1.1  2003/02/19 19:11:31  adi
-- Initial revision
--
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking,Ibit.Io,Ibit.checks;
with Measuretypes.Checks,Measuretypes.Io;
separate(If_Barometer)
procedure Command is
   type Action is (Init,Check,Start_Ibit,Stop_ibit);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Altitude,Ibit_phase);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Height,Actual_height : Measuretypes.Meter;
      Exp_Valid,Actual_Valid : Boolean;
      Exp_Phase,Actual_Phase : Ibit.Phase;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Ibit_phase =>
            Ibit.Io.Phase_Io.Get(Exp_Phase);
            Actual_Phase := Get_Ibit_State;
            Ibit.Checks.Phase(S => "If_Barometer IBIT phase",
                              Expected => Exp_Phase,
                              Actual   => Actual_Phase);
         when Altitude =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            Measuretypes.Io.Meter_Io.Get(Exp_Height);
            Get_Height(Height => Actual_Height,
                       Valid => Actual_valid);
            Test.Checking.Bool(S => "If_Barometer altitude valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Measuretypes.Checks.Meter(S => "If_Barometer altitude",
                                         Expected => Exp_Height,
                                         Actual => Actual_Height);
            end if;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Barometer Init");
         Init;
      when Start_Ibit =>
         Ada.Text_Io.Put_Line("If_Barometer start IBIT");
         Ibit_Start;
      when Stop_Ibit =>
         Ada.Text_Io.Put_Line("If_Barometer stop IBIT");
         Ibit_Stop;
      when Check =>
         Ada.Text_Io.Put("If_Barometer Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_barometer.Command");

end Command;
