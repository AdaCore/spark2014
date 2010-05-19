-- If_Destruct test i/f
--
-- $Log: if_destruct-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:34:08  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking,Destruct_Cfg.check;
separate(If_Destruct)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   package Stage_Io is new Ada.Text_Io.Enumeration_Io(Destruct_Cfg.State);

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
            Test.Checking.Bool(S => "If_Destruct stage valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Destruct_cfg.Check.State(S => "If_destruct stage",
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
         Ada.Text_Io.Put_line("If_Destruct Init");
         Init;
      when Set =>
         Ada.Text_Io.Put_line("If_Destruct Set");
         Set;
      when Check =>
         Ada.Text_Io.Put("If_Destruct Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Destruct.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Destruct.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Destruct.Command");

end Command;
