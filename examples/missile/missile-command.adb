-- Missile i/f
--
-- $Log: missile-command.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/12 20:36:55  adi
-- Initial revision
--
--
with Ada.Text_Io;
with Test_Keywords,Test.Checking, Ibit.Io, Ibit.Checks;
separate(Missile)
procedure Command is
   type Action is (Init,Check);
   package Action_Io is new Ada.Text_Io.Enumeration_io(Action);

   This_Action : Action;
   Entity : constant String := "Missile ";

   package Phase_Io is new Ada.Text_Io.Enumeration_Io(Phase_Stage);

   type Var is (Phase,component);
   package Var_Io is new Ada.Text_Io.Enumeration_Io(Var);

   type Comp_Var is (Ibit_Phase);
   package Comp_Var_Io is new Ada.Text_Io.Enumeration_Io(Comp_Var);

   package Lru_Io is new Ada.Text_Io.Enumeration_Io(Bc1553.Lru_Name);

   procedure Test_Phase(S : in String;
                        Expected, Actual : in Phase_Stage)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(Phase_Stage'Image(Actual));
      end if;
   end Test_Phase;

   procedure Check is
      This_Var : Var;
      Exp_Phase, Actual_phase : Phase_stage;
      This_Comp : Bc1553.Lru_Name;
      Field : Comp_Var;
      This_Record : Component_Status;
      Exp_Ip,Actual_Ip : Ibit.Phase;
   begin
      Var_Io.Get(This_Var);
      Ada.Text_Io.Put_Line(Var'Image(This_Var));
      case This_Var is
         when phase =>
            Phase_Io.Get(Exp_Phase);
            Actual_Phase := State.Phase;
            Test_Phase("Missile phase",Exp_Phase,Actual_Phase);
         when Component =>
            Lru_Io.Get(This_Comp);
            Comp_Var_Io.Get(Field);
            This_Record := State.Components(This_Comp);
            case Field is
               when Ibit_Phase =>
                  Ibit.Io.Phase_Io.Get(Exp_Ip);
                  Actual_Ip := This_Record.Bit_Phase;
                  Ibit.Checks.Phase(S => "Missile component " &
                                    Bc1553.Lru_Name'Image(This_Comp) &
                                    " bit phase",
                                    Expected => Exp_Ip,
                                    Actual => Actual_Ip);
            end case;
      end case;
   end Check;

begin
   Action_Io.Get(This_Action);
   case This_Action is
      when Init =>
         Ada.Text_Io.Put_line(Entity & "Init");
         Init;
      when Check =>
         Ada.Text_Io.Put(Entity & "Check ");
         Check;
   end case;
   Ada.Text_Io.Skip_Line;
end Command;
