-- Radar i/f
--
-- $Log: radar-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/25 13:57:28  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking, State_Types.Io,
   State_Types.Check, Measuretypes.Checks, Measuretypes.io;
separate(Radar)
procedure Command is
   package Sector_Io is new Ada.Text_Io.Integer_Io(Radar_Cfg.Sector_Range);

   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Radar ";

   type Var is (distance,Velocity,Sector_contact);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Distance,Actual_Distance : Meter;
      Exp_Sector_X, Exp_Sector_y : Sector;
      Exp_Speed, Actual_Speed : Meter_Per_Sec;
  begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Distance =>
            Sector_Io.Get(Exp_Sector_x);
            Sector_Io.Get(Exp_Sector_y);
            Measuretypes.Io.Meter_Io.Get(Exp_Distance);
            Read_Location(Sx => Exp_Sector_X,
                          Sy => Exp_Sector_Y,
                          D => Actual_Distance,
                          V => Actual_Speed);
            Measuretypes.Checks.Meter(S => "Sector (" &
                                     Sector'Image(Exp_Sector_X) &
                                     "," &
                                     Sector'Image(Exp_Sector_Y) &
                                     ") distance",
                                     Expected => Exp_Distance,
                                     Actual => Actual_distance);
         when velocity =>
            Sector_Io.Get(Exp_Sector_x);
            Sector_Io.Get(Exp_Sector_y);
            Measuretypes.Io.speed_Io.Get(Exp_speed);
            Read_Location(Sx => Exp_Sector_X,
                          Sy => Exp_Sector_Y,
                          D => Actual_Distance,
                          V => Actual_Speed);
            Measuretypes.Checks.Meter_Per_sec(S => "Sector (" &
                                     Sector'Image(Exp_Sector_X) &
                                     "," &
                                     Sector'Image(Exp_Sector_Y) &
                                     ") speed",
                                     Expected => Exp_speed,
                                     Actual => Actual_speed);
         when Sector_contact =>
            null;
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      Exp_Distance : Meter;
      Exp_Sector_X, Exp_Sector_y : Sector;
      Exp_Speed : Meter_Per_Sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Distance | velocity =>
            null;
         when Sector_Contact =>
            Sector_Io.Get(Exp_Sector_x);
            Sector_Io.Get(Exp_Sector_y);
            Measuretypes.Io.Meter_Io.Get(Exp_Distance);
            Measuretypes.Io.speed_Io.Get(Exp_speed);
            Set_Bearing_Return(Sx => Exp_Sector_X,
                          Sy => Exp_Sector_Y,
                          D => exp_Distance,
                          V => exp_Speed);
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
