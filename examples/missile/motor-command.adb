-- Motor i/f
--
-- $Log: motor-command.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/01 18:27:13  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,
  Measuretypes.Checks;
separate(Motor)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Motor ";

   package power_Io is new Ada.Text_Io.Integer_Io(Power);

   type Var is (thrust);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Power, Actual_Power : Power;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when thrust =>
            power_Io.Get(Exp_power);
            Read_thrust(This_Level => Actual_Power);
            Measuretypes.Checks.Newton(S => Entity,
                                       Expected => Exp_Power,
                                       Actual => Actual_Power,
                                       Margin  => 10);
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
            Power_Io.Get(This_Power);
            Set_thrust(This_Power);
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
