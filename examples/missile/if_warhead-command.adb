-- If_Warhead test i/f
--
-- $Log: if_warhead-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:29:09  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking,Warhead_Cfg.check;
separate(If_Warhead)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   package Stage_Io is new Ada.Text_Io.Enumeration_Io(Warhead_Cfg.State);

   type Var is (Fire_Stage);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_State,Actual_State : Stage;
      Exp_Valid, Actual_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Fire_stage =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            Stage_Io.Get(Exp_State);
            Get_Stage(Action_Stage => Actual_State,
                      Valid => Actual_Valid);
            Test.Checking.Bool(S => "If_Warhead stage valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Warhead_cfg.Check.State(S => "If_warhead stage",
                                       Expected => Exp_state,
                                       Actual => Actual_state);
            end if;
      end case;
   end Check;

   procedure set is
      This_Var : Var;
      this_State : Stage;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Fire_stage =>
            Stage_Io.Get(this_State);
            Set_Stage(New_Stage => This_State);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Warhead Init");
         Init;
      when Set =>
         Ada.Text_Io.Put_line("If_Warhead Set");
         Set;
      when Check =>
         Ada.Text_Io.Put("If_Warhead Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Warhead.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Warhead.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Warhead.Command");

end Command;
