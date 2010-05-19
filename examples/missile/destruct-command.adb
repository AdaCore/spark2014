-- Destruct i/f
--
-- $Log: destruct-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 19:22:48  adi
-- Initial revision
--
--
with Ada.Text_Io,Destruct_Cfg.check;
with Test_Keywords,Test.Checking;
separate(Destruct)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Destruct ";

   package Stage_Io is new Ada.Text_Io.Enumeration_Io(Stage);

   type Var is (Fire_Stage,timer);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_State, Actual_State : Stage;
      Exp_Timer, Actual_Timer : Clock.Millisecond;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Fire_Stage =>
            Stage_Io.Get(Exp_State);
            Read_stage(Actual_state);
            Destruct_cfg.Check.state(S => Entity,
                                    Expected => Exp_state,
                                    Actual => Actual_state);
         when timer =>
            Test_Keywords.millisec_Io.get(Exp_timer);
            Actual_timer := Stage_timer;
            Test.checking.time(S => Entity,
                               Expected => Exp_timer,
                               Actual => Actual_timer);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      New_state : Stage;
      New_Time : Clock.Millisecond;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Fire_Stage =>
            Stage_Io.Get(New_state);
            Set_stage(New_state);
         when Timer =>
            Test_Keywords.Millisec_Io.get(New_time);
            Set_timer(New_time);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line(Entity & "Init");
         Init;
      when Check =>
         Ada.Text_Io.Put(Entity & "Check ");
         Check;
      when Set =>
        Ada.Text_Io.Put(Entity & "Set ");
        Set;
   end case;
   Ada.Text_Io.Skip_Line;
end Command;
