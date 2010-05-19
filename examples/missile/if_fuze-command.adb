-- If_Fuze test i/f
--
-- $Log: if_fuze-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/18 17:58:09  adi
-- Corrected output
--
-- Revision 1.1  2003/08/17 15:29:36  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking,State_Types.Io,State_Types.check;
separate(If_Fuze)
procedure Command is
   type Action is (Init,Check,Arm,disarm);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Action_state);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_State,Actual_State : State_Types.Fuze;
      Exp_Valid, Actual_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Action_state =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            State_Types.Io.Fuze_Io.Get(Exp_State);
            Get_State(Action_State => Actual_State,
                      Valid => Actual_Valid);
            Test.Checking.Bool(S => "If_Fuze state valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               State_types.Check.fuze(S => "If_fuze state",
                                      Expected => Exp_state,
                                      Actual => Actual_state);
            end if;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Fuze Init");
         Init;
      when Arm =>
         Ada.Text_Io.Put_line("If_Fuze arm");
         arm;
      when Disarm =>
         Ada.Text_Io.Put_line("If_Fuze disarm");
         disarm;
      when Check =>
         Ada.Text_Io.Put("If_Fuze Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Fuze.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Fuze.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Fuze.Command");

end Command;
