-- Infrared i/f
--
-- $Log: ir-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/27 21:07:49  adi
-- Changed label
--
-- Revision 1.1  2003/08/27 20:51:50  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking, State_Types.Io,
   State_Types.Check, Measuretypes.Checks, Measuretypes.io;
separate(ir)
procedure Command is
   package Sector_Io is new Ada.Text_Io.Integer_Io(ir_Cfg.Sector_Range);

   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Infrared ";

   type Var is (temperature,Sector_contact);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_temp,Actual_temp : kelvin;
      Exp_Sector_X, Exp_Sector_y : Sector;
  begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when temperature =>
            Sector_Io.Get(Exp_Sector_x);
            Sector_Io.Get(Exp_Sector_y);
            Measuretypes.Io.Kelvin_Io.Get(Exp_Temp);
            Read_Location(Sx => Exp_Sector_X,
                          Sy => Exp_Sector_Y,
                          T => Actual_Temp);
            Measuretypes.Checks.Kelvin(S => "Sector (" &
                                     Sector'Image(Exp_Sector_X) &
                                     "," &
                                     Sector'Image(Exp_Sector_Y) &
                                     ") temp ",
                                     Expected => Exp_temp,
                                     Actual => Actual_temp);
         when Sector_contact =>
            null;
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      Exp_temp : Kelvin;
      Exp_Sector_X, Exp_Sector_y : Sector;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when temperature =>
            null;
         when Sector_Contact =>
            Sector_Io.Get(Exp_Sector_x);
            Sector_Io.Get(Exp_Sector_y);
            Measuretypes.Io.kelvin_Io.Get(Exp_temp);
            Set_Cell_Return(Sx => Exp_Sector_X,
                            Sy => Exp_Sector_Y,
                            T => Exp_Temp);
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
