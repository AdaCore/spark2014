-- Fuze i/f
--
-- $Log: fuze-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/17 14:35:26  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking, State_Types.Io,
   State_Types.check;
separate(Fuze)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Fuze ";

   type Var is (State,timer);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_State, Actual_State : State_Types.Fuze;
      Exp_Timer,Actual_Timer : Clock.Millisecond;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when state =>
            State_Types.Io.Fuze_Io.Get(Exp_State);
            Read_state(Actual_state);
            State_Types.Check.fuze(S => Entity,
                                   Expected => Exp_state,
                                   Actual => Actual_state);
         when timer =>
            Test_Keywords.millisec_Io.get(Exp_timer);
            Actual_timer := State_timer;
            Test.checking.time(S => Entity,
                               Expected => Exp_timer,
                               Actual => Actual_timer);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      New_state : State_Types.Fuze;
      New_Time : Clock.Millisecond;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when state =>
            State_Types.Io.fuze_Io.Get(New_state);
            Set_state(New_state);
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
