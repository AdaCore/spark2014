-- If_Steer test i/f
--
-- $Log: if_steer-command.adb,v $
-- Revision 1.2  2004/12/18 12:24:21  adi
-- Added margin parameter for integer comparison
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/31 20:35:11  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking;
separate(If_Steer)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (deflection);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   package Fin_Io is new Ada.Text_Io.Enumeration_Io(Fin);
   package Angle_Io is new Ada.Text_Io.Integer_Io(Angle);

   procedure Check is
      This_Var : Var;
      Exp_Angle,Actual_Angle : Angle;
      This_Fin : Fin;
      Exp_Valid, Actual_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when deflection =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            Fin_Io.Get(This_Fin);
            Angle_Io.Get(Exp_Angle);
            Get_Deflection(For_Fin => This_Fin,
                           This_Angle => Actual_Angle,
                           Valid => Actual_Valid);
            Test.Checking.Bool(S => "If_Steer state valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
               Test.Checking.Signed16
                 (S        => "If_steer state",
                  Expected => Systemtypes.Signed16(Exp_Angle),
                  Actual   => Systemtypes.Signed16(Actual_angle),
                  Margin   => 0);
            end if;
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      This_Angle : Angle;
      This_Fin : Fin;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when deflection =>
            Fin_Io.Get(This_Fin);
            Angle_Io.Get(this_Angle);
            Set_Deflection(For_Fin => This_Fin,
                           New_Angle => This_Angle);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Steer Init");
         Init;
      when Set =>
         Ada.Text_Io.Put_line("If_Steer Set");
         Set;
      when Check =>
         Ada.Text_Io.Put("If_Steer Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Steer.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Steer.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Steer.Command");

end Command;
