-- Ins i/f
--
-- $Log: ins-command.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/10 22:04:36  adi
-- Initial revision
--
--
--
with 
  Ada.Text_Io,
  Test_Keywords,
  Test.Checking,
  Cartesian.Io, 
  Cartesian.Check;
separate(Ins)
procedure Command is
   type Action is (Init,Check,Set);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Position,Velocity,offset);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Position, Actual_Position : Cartesian.Position;
      Exp_Velocity, Actual_Velocity : Cartesian.Velocity;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Position =>
            Cartesian.IO.Get_Position(Exp_Position);
            Read_Location(X => Actual_Position.X,
                          Y => Actual_Position.Y,
                          Z => Actual_Position.Z);
            Cartesian.Check.Position
	      (S        => "Ins ",
	       Expected => Exp_Position,
	       Actual   => Actual_Position,
	       Margin   => 10);
         when Velocity =>
            Cartesian.Io.Get_Velocity(Exp_Velocity);
            Actual_Velocity := Last_Velocity;
            Cartesian.Check.Velocity
	      (S        => "Ins ",
	       Expected => Exp_velocity,
	       Actual   => Actual_velocity,
	       Margin   => 5);
         when Offset =>
            -- Can't check this; ignore it
            null;
      end case;
   end Check;

   procedure Set is
      This_Var : Var;
      New_Position : Cartesian.Position;
      New_Velocity : Cartesian.Velocity;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when position =>
            Cartesian.Io.Get_Position(New_Position);
            Set_Location(X => New_Position.X,
                         Y => New_Position.Y,
                         Z => New_Position.Z);
         when Velocity =>
            Cartesian.Io.Get_Velocity(V => New_Velocity);
            Set_Velocity(vX => New_Velocity.vX,
                         vY => New_Velocity.Vy,
                         vZ => New_Velocity.Vz);
         when Offset =>
            Cartesian.Io.Get_Position(New_Position);
            Move(Dx => New_Position.X,
                 Dy => New_Position.Y,
                 Dz => New_Position.Z);
      end case;
   end Set;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("Ins Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("Ins Check ");
         Check;
      when Set =>
        Ada.Text_Io.Put("Ins Set ");
        Set;
   end case;
   Ada.Text_Io.Skip_Line;
end Command;
