
-- If_Radar test i/f
--
-- $Log: if_ir-command.adb,v $
-- Revision 1.2  2004/12/18 12:24:21  adi
-- Added margin parameter for integer comparison
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/27 21:05:01  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking,
  State_Types.Io,State_Types.Check,
  Measuretypes.Io, Measuretypes.checks;
separate(If_Ir)
procedure Command is
   type Action is (Init,Check,Fire_stare,Fire_Sweep);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);
   This_Action : Action;

   package Sector_Io is new Ada.Text_Io.Integer_Io(ir_Cfg.Sector_Range);

   type Var is (stare,sweep);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   procedure Check is
      This_Var : Var;
      Exp_Sx,Exp_Sx2,Exp_Sy,Exp_sy2 : Sector;
      Actual_Sx,Actual_Sx2,Actual_Sy,Actual_sy2 : Sector;
      Exp_Temp, Actual_Temp : Measuretypes.Kelvin;
      Exp_Grid,Actual_grid : Measuretypes.Bit4_Array;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when Sweep =>
            Sector_Io.Get(Exp_Sx);
            Sector_Io.Get(Exp_Sx2);
            Sector_Io.Get(Exp_Sy);
            Sector_Io.Get(Exp_Sy2);
            -- Read in the expected grid
            for X in Measuretypes.Bit4_Range loop
               for Y in Measuretypes.Bit4_Range loop
                  Test_Keywords.Bool_Io.Get(Exp_Grid(X)(Y));
               end loop;
            end loop;
            Read_Sweep(Actual_Sx,Actual_Sx2,Actual_Sy,Actual_Sy2,
                       Actual_Grid);
            -- Now compare
            Test.Checking.Signed16
              (S => "Sweep Sx_Start",
               Expected => Systemtypes.Signed16(Exp_Sx),
               Actual   => Systemtypes.Signed16(Actual_Sx),
               Margin   => 0);
            Test.Checking.Signed16
              (S        => "Sweep Sx_End",
               Expected => Systemtypes.Signed16(Exp_Sx2),
               Actual   => Systemtypes.Signed16(Actual_Sx2),
               Margin   => 0);
            Test.Checking.Signed16
              (S        => "Sweep Sy_Start",
               Expected => Systemtypes.Signed16(Exp_Sy),
               Actual   => Systemtypes.Signed16(Actual_Sy),
               Margin   => 0);
            Test.Checking.Signed16
              (S        => "Sweep Sy_End",
               Expected => Systemtypes.Signed16(Exp_Sy2),
               Actual   => Systemtypes.Signed16(Actual_Sy2),
               Margin   => 0);
            Measuretypes.Checks.Bit4_array("Sweep grid",
                                           Exp_Grid,
                                           Actual_Grid);
         when stare =>
            Sector_Io.Get(Exp_Sx);
            Sector_Io.Get(Exp_Sy);
            Measuretypes.Io.Kelvin_Io.Get(Exp_Temp);
            Read_Stare(Actual_Sx,Actual_Sy,actual_temp);
            -- Now compare bits
            Test.Checking.Signed16
              (S        => "Stare Sx",
               Expected => Systemtypes.Signed16(Exp_Sx),
               Actual   => Systemtypes.Signed16(Actual_Sx),
               Margin   => 0);
            Test.Checking.Signed16
              (S        => "Stare Sy",
               Expected => Systemtypes.Signed16(Exp_Sy),
               Actual   => Systemtypes.Signed16(Actual_Sy),
               Margin   => 0);
            Measuretypes.Checks.Kelvin("Stare temperature",
                                      Exp_Temp,
                                      Actual_temp);
      end case;
   end Check;

   procedure Do_stare is
      Sx,Sy : Sector;
   begin
      Sector_Io.Get(Sx);
      Sector_Io.Get(Sy);
      Stare(Sx => Sx, Sy => Sy);
   end Do_stare;

   procedure Do_Sweep is
      Sx1,Sx2,sy1,Sy2 : Sector;
   begin
      Sector_Io.Get(Sx1);
      Sector_Io.Get(Sx2);
      Sector_Io.Get(Sy1);
      Sector_Io.Get(Sy2);
      Sweep(Sx_start => Sx1,
           Sx_End   => Sx2,
           Sy_start => Sy1,
           Sy_End   => sy2);
   end Do_Sweep;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line("If_ir Init");
         Init;
      when Fire_Stare =>
         Ada.Text_Io.Put_line("If_ir Stare");
         Do_Stare;
      when Fire_Sweep =>
         Ada.Text_Io.Put_line("If_ir Sweep");
         Do_Sweep;
      when Check =>
         Ada.Text_Io.Put("If_ir Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;

exception
   when Ada.Text_Io.Data_Error =>
      Ada.Text_Io.Put_Line("Data_Error in If_ir.Command");
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in If_ir.Command");
   when others =>
      Ada.Text_Io.Put_Line("Unknown exception in If_ir.Command");

end Command;
