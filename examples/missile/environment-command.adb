-- Testpoint for Environment
--
-- $Log: environment-command.adb,v $
-- Revision 1.3  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/11 19:57:50  adi
-- Initial revision
--
--
with 
  Ada.Text_Io,
  Test_Keywords,
  Cartesian.Io,
  Cartesian.Check, 
  Test,
  Measuretypes.Checks;
separate(Environment)
procedure Command is
   type environment_Keyword is (Add,Delete,check);
   type Property_keyword is (Position,Velocity,Object_kind,Radar_xsection);

   package environment_Io is new
     Ada.Text_Io.Enumeration_Io(environment_Keyword);
   package Property_Io is new
     Ada.Text_Io.Enumeration_Io(Property_Keyword);
   package Kind_Io is new
     Ada.Text_Io.Enumeration_Io(Kind);
   package Rcs_Io is new
     Ada.Text_Io.Integer_Io(Rcs);
   package Handle_Io is new
     Ada.Text_Io.Integer_Io(Handle);

   Action : environment_Keyword;
   H : Handle;
   Exp_P, Actual_p : Cartesian.Position;
   Exp_V, Actual_v : Cartesian.Velocity;
   Exp_K, Actual_k : Kind;
   Exp_R, Actual_r : Rcs;
   Pp : Property_Keyword;
   Obj : Object;

   procedure Check_Kind(S : in String;
                        Expected, Actual : in Kind)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail(Kind'Image(Actual));
      end if;
   end Check_Kind;

begin
   environment_Io.Get(Action);
   case Action is
      when add =>
         Ada.Text_Io.Put_Line("Add environment object");
         Cartesian.Io.Get_Position(Actual_P);
         Cartesian.Io.Get_Velocity(Actual_V);
         Kind_Io.Get(Actual_K);
         Rcs_Io.Get(Actual_R);
         Add_Object(P => Actual_P,
                    V => Actual_V,
                    K => Actual_K,
                    R => Actual_R,
                    H => H);
         if H not in Valid_Handle then
            Ada.Text_Io.Put_Line("   created with ID " &
                            Handle'Image(H));
         else
            Ada.Text_Io.Put_Line("FAILED to create environment object");
         end if;
      when Check =>
         Property_Io.Get(Pp);
         Handle_Io.Get(H);
         Obj := Object_array(H);
         case Pp is
            when Position =>
               Cartesian.Io.Get_Position(Exp_P);
               Get_Object_Position
		 (H => H,
		  P => Actual_P);
               Cartesian.Check.Position
		 (S        => "Object " & Handle'Image(H) & " position",
		  Expected => Exp_P,
		  Actual   => Actual_P,
		  Margin   => 10);
            when Velocity =>
               Cartesian.Io.Get_Velocity(Exp_v);
               Get_Object_velocity
		 (H => H,
		  V => Actual_v);
               Cartesian.Check.Velocity
		 (S        => "Object " & Handle'Image(H) & " velocity",
		  Expected => Exp_v,
		  Actual   => Actual_v,
		  Margin   => 5);
            when Object_Kind =>
               Kind_Io.Get(Exp_K);
               Actual_K := Obj.K;
               Check_Kind
		 (S        => "Object " & Handle'Image(H) & " kind",
		  Expected => Exp_K,
		  Actual   => Actual_K);
            when Radar_xsection =>
               Rcs_Io.Get(Exp_R);
               Actual_R := Obj.R;
               Measuretypes.Checks.Meter_2
		 (S        => "Object " & Handle'Image(H) & " RCS",
		  Expected => Exp_R,
		  Actual   => Actual_R);
         end case;
      when delete =>
         Ada.Text_Io.Put_Line("Delete environment object");
         Handle_Io.Get(H);
         Delete_Object(H);
   end case;
   Ada.Text_Io.skip_Line;
exception
   when Constraint_Error =>
      Ada.Text_Io.Put_Line("Constraint_Error in Environment Command");
   when Ada.Text_Io.Data_error =>
      Ada.Text_Io.Put_Line("Data_Error in Environment Command");
   when others =>
      Ada.Text_Io.Put_Line("Exception in Environment Command");
end Command;
