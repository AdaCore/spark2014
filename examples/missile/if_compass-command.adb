-- If_Compass test i/f
--
-- $Log: if_compass-command.adb,v $
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
-- Revision 1.2  2003/08/06 20:44:57  adi
-- Added more exception catches
--
-- Revision 1.1  2003/08/02 19:33:47  adi
-- Initial revision
--
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking;
with Measuretypes.Checks;
with Measuretypes.Io;
separate(If_Compass)
procedure Command is
   type Action is (Init,Check);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Angle_XY,Angle_YZ);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_XY, Exp_YZ : Measuretypes.Angle_Degrees;
      Actual_XY : Measuretypes.Millirad;
      Exp_XY_Valid,Actual_XY_Valid : Boolean;
      Actual_YZ : Measuretypes.Millirad;
      Exp_YZ_Valid,Actual_YZ_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Angle_XY =>
            Test_Keywords.Bool_Io.Get(Exp_XY_Valid);
            Measuretypes.Io.Angle_Io.Get(Exp_XY);
            Get_XY(Angle => Actual_XY,
                   Valid => Actual_XY_Valid);
            Test.Checking.Bool(S => "If_Compass XY angle valid",
                               Expected => Exp_XY_Valid,
                               Actual => Actual_XY_Valid);
            if Exp_XY_Valid and Actual_XY_Valid then
               Measuretypes.Checks.Angle_Degrees_Millirads
                 (S        => "If_Compass XY angle",
                  Expected => Exp_XY,
                  Actual   => Actual_XY);
            end if;
         when Angle_YZ =>
            Test_Keywords.Bool_Io.Get(Exp_YZ_Valid);
            Measuretypes.Io.Angle_Io.Get(Exp_YZ);
            Get_XY(Angle => Actual_YZ,
                   Valid => Actual_YZ_Valid);
            Test.Checking.Bool(S => "If_Compass YZ angle valid",
                               Expected => Exp_YZ_Valid,
                               Actual => Actual_YZ_Valid);
            if Exp_YZ_Valid and Actual_YZ_Valid then
               Measuretypes.Checks.Angle_Degrees_Millirads
                 (S        => "If_Compass YZ angle",
                  Expected => Exp_YZ,
                  Actual   => Actual_YZ);
            end if;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Compass Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("If_Compass Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Compass.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Compass.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Compass.Command");

end Command;
