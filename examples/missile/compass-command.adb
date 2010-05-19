-- Compass test i/f
--
-- $Log: compass-command.adb,v $
-- Revision 1.4  2004/12/17 17:51:22  adi
-- Fixed compass angle conversions and checks so that compass.in passes
--
-- Revision 1.3  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/08 20:32:02  adi
-- Use of Angle_Ops
--
-- Revision 1.1  2003/08/05 18:49:44  adi
-- Initial revision
--
--
--
with Ada.Text_Io;
with Measuretypes.Checks;
with Measuretypes.Io;
separate(Compass)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (XY,DXY,YZ,DYZ);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   Unit_Name : constant String := "Compass";

   procedure Check is
      This_Var       : Var;
      Actual_Degrees : Measuretypes.Angle_Degrees;
      Exp_Angle      : Measuretypes.Angle_Degrees;
      Exp_Delta,
        Actual_Delta : Measuretypes.Millirad_Per_Sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when XY =>
            Measuretypes.Io.Angle_Io.Get(Exp_angle);
            Read_XY(Actual_degrees);
            Measuretypes.Checks.Angle_Degrees
              (S        => Unit_Name & " " & Var'Image(This_Var),
               Expected => Exp_angle,
               Actual   => Actual_degrees);
         when YZ =>
            Measuretypes.io.Angle_Io.Get(Exp_angle);
            Read_YZ(Actual_degrees);
            Measuretypes.Checks.Angle_Degrees
              (S => Unit_Name & " " & Var'Image(This_Var),
               Expected => Exp_angle,
               Actual => Actual_degrees);
         when DXY =>
            Measuretypes.Io.Angle_Rate_Io.Get(Exp_Delta);
            Read_Dxy(Actual_Delta);
            Measuretypes.Checks.Millirad_Per_Sec
              (S        => Unit_Name & " " & Var'Image(This_Var),
               Expected => Exp_Delta,
               Actual   => Actual_Delta);
         when DYZ =>
            Measuretypes.Io.Angle_Rate_Io.Get(Exp_Delta);
            Read_DYZ(Actual_Delta);
            Measuretypes.Checks.Millirad_Per_Sec
              (S        => Unit_Name & " " & Var'Image(This_Var),
               Expected => Exp_Delta,
               Actual   => Actual_Delta);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      New_Angle : Measuretypes.Angle_Degrees;
      New_Delta : Measuretypes.Millirad_Per_Sec;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when XY =>
            Measuretypes.Io.Angle_Io.Get(New_angle);
            Set_XY(XY => new_angle);
         when dXY =>
            Measuretypes.Io.Angle_Rate_Io.Get(New_delta);
            Set_dXY(dXY => new_delta);
         when YZ =>
            Measuretypes.Io.Angle_Io.Get(New_angle);
            Set_YZ(YZ => new_angle);
         when dYZ =>
            Measuretypes.Io.Angle_Rate_Io.Get(New_delta);
            Set_dYZ(dYZ => new_delta);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   ada.text_io.put(Unit_name);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line(" Init");
         Init;
      when Check =>
         Ada.Text_Io.Put(" Check ");
         Check;
      when Set =>
        Ada.Text_Io.Put(" Set ");
        Set;
   end case;
   Ada.Text_Io.Skip_Line;
end Command;
