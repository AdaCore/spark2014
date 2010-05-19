-- If_Ins test i/f
--
-- $Log: if_ins-command.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/12 18:09:26  adi
-- Initial revision
--
--
with 
  Ada.Text_Io,
  Cartesian.Io,
  Cartesian.Check,
  Test_Keywords,
  Test.Checking;
separate(If_Ins)
procedure Command is
   type Action is (Init,Check);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   type Var is (Location);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Location, Actual_location : Cartesian.Position;
      Exp_Valid, Actual_Valid : Boolean;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Location =>
            Test_Keywords.Bool_Io.Get(Exp_Valid);
            Cartesian.Io.Get_position(Exp_Location);
            Get_Location(Position => Actual_Location,
                         Valid => Actual_Valid);
            Test.Checking.Bool(S => "If_Ins location valid",
                               Expected => Exp_Valid,
                               Actual => Actual_Valid);
            if Exp_Valid and Actual_Valid then
	       Cartesian.Check.Position
		 (S        => "If_Ins location",
		  Expected => Exp_location,
		  Actual   => Actual_location,
		  Margin   => 10);
            end if;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_Ins Init");
         Init;
      when Check =>
         Ada.Text_Io.Put("If_Ins Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_Ins.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_Ins.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_Ins.Command");

end Command;
