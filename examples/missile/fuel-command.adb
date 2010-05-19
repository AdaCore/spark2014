-- Fuel system test interface
--
-- $Log: fuel-command.adb,v $
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
-- Revision 1.1  2003/08/17 12:42:27  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking;
with Measuretypes.Checks, Measuretypes.Io;
separate(Fuel)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Fuel ";

   type Var is (Level,rate);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Level, Actual_Level : kilo;
      Exp_Rate, Actual_Rate : Gram_Per_Sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Level =>
            Measuretypes.Io.Mass_IO.Get(Exp_Level);
            Read_Level(Actual_Level);
            Measuretypes.Checks.Kilo(S => Entity,
                                     Expected => Exp_Level,
                                     Actual => Actual_Level);
         when Rate =>
            Measuretypes.Io.Gram_Rate_Io.get(Exp_Rate);
            Actual_Rate := Last_Rate;
            Measuretypes.Checks.Gram_Per_Sec(S => Entity,
                                             Expected => Exp_rate,
                                             Actual => Actual_rate);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      New_Level : Kilo;
      New_Rate : Gram_Per_Sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when level =>
            Measuretypes.Io.Mass_Io.Get(New_Level);
            Set_Level(New_Level);
         when Rate =>
            Measuretypes.Io.Gram_Rate_Io.get(New_Rate);
            Set_Rate(New_Rate);
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
