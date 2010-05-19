-- Steer i/f
--
-- $Log: steer-command.adb,v $
-- Revision 1.2  2004/12/18 12:24:21  adi
-- Added margin parameter for integer comparison
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/31 20:11:13  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking, State_Types.Io,
   State_Types.check;
separate(Steer)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;
   Entity : constant String := "Steer ";

   package Fin_Io is new Ada.Text_Io.Enumeration_io(Steer_Cfg.Fin);
   package Angle_Io is new Ada.Text_Io.Integer_Io(Steer_Cfg.Fin_Angle);

   type Var is (Deflection);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Angle,Actual_Angle : Angle;
      This_Fin : Fin;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when deflection =>
            Fin_Io.Get(This_Fin);
            Angle_Io.Get(Exp_Angle);
            Read_Deflection(For_Fin    => This_Fin,
                            This_Angle => Actual_Angle);
            Test.checking.Signed16
              (S        => Entity,
               Expected => Systemtypes.Signed16(Exp_Angle),
               Actual   => Systemtypes.Signed16(Actual_Angle),
               Margin   => 1);
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      This_Fin : Fin;
      this_Angle : Angle;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when deflection =>
            Fin_Io.Get(This_Fin);
            Angle_Io.Get(This_Angle);
            Set_Deflection(For_Fin => This_Fin,
                           New_Angle => This_Angle);
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
