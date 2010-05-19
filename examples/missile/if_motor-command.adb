-- If_Motor test i/f
--
-- $Log: if_motor-command.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:29:01  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Measuretypes.Io,Measuretypes.Checks,Test.Checking,Test_keywords;
separate(If_Motor)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   package Power_Io is new Ada.Text_Io.Integer_Io(Power);

   type Var is (Thrust);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Power,Actual_Power : Power;
      Exp_Valid, Actual_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when thrust =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            Power_Io.Get(Exp_Power);
            Get_Thrust(This_Level => Actual_Power,
                       Valid => Actual_Valid);
            Test.Checking.Bool(S => "If_Motor thrust valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Measuretypes.Checks.Newton
                 (S        => "If_motor thrust",
                  Expected => Exp_power,
                  Actual   => Actual_Power,
                  Margin   => 10);
            end if;
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      This_Power : Power;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when thrust =>
            Power_Io.Get(this_Power);
            Set_Thrust(New_Level => This_Power);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Motor Init");
         Init;
      when Set =>
         Ada.Text_Io.Put_line("If_Motor Set");
         Set;
      when Check =>
         Ada.Text_Io.Put("If_Motor Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Motor.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Motor.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Motor.Command");

end Command;
