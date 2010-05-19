-- If_Fuel test i/f
--
-- $Log: if_fuel-command.adb,v $
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/18 18:16:42  adi
-- Use measuretypes.io
--
-- Revision 1.1  2003/08/17 12:51:22  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Measuretypes.io,Test.Checking,Test_keywords;
with Measuretypes.Checks;
separate(If_Fuel)
procedure Command is
   type Action is (Init,Check);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Level);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Level, Actual_level : Measuretypes.Kilo;
      Exp_Valid, Actual_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Level =>
            Test_keywords.Bool_Io.Get(Exp_Valid);
            Measuretypes.io.Mass_Io.Get(Exp_Level);
            get_Level(level => Actual_Level,
                       Valid => Actual_Valid);
            Test.Checking.Bool(S => "If_Fuel level valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Measuretypes.Checks.Kilo(S => "If_Fuel level",
                                        Expected => Exp_level,
                                        Actual => Actual_level);
            end if;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Fuel Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("If_Fuel Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Fuel.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Fuel.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Fuel.Command");

end Command;
