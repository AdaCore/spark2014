------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    F L O W . A N T I A L I A S I N G                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Nlists;   use Nlists;
with Sem_Util; use Sem_Util;

--  with Treepr; use Treepr;
--  with Output; use Output;
--  with Sprint; use Sprint;
with Errout; use Errout;

with Why;

package body Flow.Antialiasing is

   type Aliasing_Check_Result is (No_Aliasing,
                                  Possible_Aliasing,
                                  Definite_Aliasing);

   function Aliasing (A, B : Node_Id) return Aliasing_Check_Result;
   --  Returns if A and B alias.

   procedure Check_Node_Against_Node
     (A, B                : Node_Or_Entity_Id;
      A_Formal            : Entity_Id;
      B_Formal            : Entity_Id;
      Introduces_Aliasing : in out Boolean)
   with Pre => Present (A_Formal);
   --  Checks the two nodes for aliasing and issues an error message
   --  if appropriate. The formal for B can be Empty, in which case we
   --  assume it is a global.

   procedure Check_Parameter_Against_Parameters_And_Globals
     (Actual              : Node_Id;
      Introduces_Aliasing : in out Boolean);
   --  Checks the given actual against all other parameters and
   --  globals.

   --------------
   -- Aliasing --
   --------------

   function Aliasing (A, B : Node_Id) return Aliasing_Check_Result
   is
      pragma Unreferenced (A, B);
   begin
      return No_Aliasing;
   end Aliasing;

   -----------------------------
   -- Check_Node_Against_Node --
   -----------------------------

   procedure Check_Node_Against_Node
     (A, B                : Node_Or_Entity_Id;
      A_Formal            : Entity_Id;
      B_Formal            : Entity_Id;
      Introduces_Aliasing : in out Boolean)
   is
      Msg : Unbounded_String := Null_Unbounded_String;
   begin
      --  Write_Str ("AA: Checking ");
      --  Sprint_Node (A);
      --  Write_Str (" <--> ");
      --  Sprint_Node (B);
      --  Write_Eol;

      case Aliasing (A, B) is
         when No_Aliasing =>
            --  Nothing to do here.
            return;

         when Possible_Aliasing =>
            Append (Msg, "possible ");

         when Definite_Aliasing =>
            null;
      end case;

      Introduces_Aliasing := True;

      Append (Msg, "aliasing between formal parameter");
      if Present (B_Formal) then
         Append (Msg, "s & and &");
         Error_Msg_Node_2 := B_Formal;
      else
         Append (Msg, " & and global &");
         Error_Msg_Node_2 := B;
      end if;
      Append (Msg, "!");

      Error_Msg_NE (To_String (Msg), A, A_Formal);
   end Check_Node_Against_Node;

   ----------------------------------------------------
   -- Check_Parameter_Against_Parameters_And_Globals --
   ----------------------------------------------------

   procedure Check_Parameter_Against_Parameters_And_Globals
     (Actual              : Node_Id;
      Introduces_Aliasing : in out Boolean)
   is
      Formal : Entity_Id;
      Call   : Node_Id;
      Is_Out : Boolean;
   begin

      --  Work out who we are.

      Find_Actual (Actual, Formal, Call);
      Is_Out := Ekind (Formal) in E_Out_Parameter | E_In_Out_Parameter;

      --  The general idea here is to make sure none of the globals
      --  and parameters overlap. If we have a procedure with
      --  parameters X, Y and Z and globals A and B, then we check the
      --  following:
      --
      --     X v.s. (Y, Z, A, B)
      --     Y v.s. (   Z, A, B)
      --     Z v.s. (      A, B)
      --
      --  In particular we do not check the globals against each other
      --  and we do not check combinations of parameters which we have
      --  already seen. This is implemented by this procedure having
      --  the same loop as
      --  Check_Parameter_Against_Parameters_And_Globals and by only
      --  checking parameters once we have seen our parameter we
      --  compare against.

      --  Check against parameters.

      declare
         P            : Node_Id;
         Other        : Node_Id;
         Other_Formal : Entity_Id;
         Other_Call   : Node_Id;
         Other_Is_Out : Boolean;
         Found_Myself : Boolean := False;
      begin
         P := First (Parameter_Associations (Call));
         while Present (P) loop
            if Nkind (P) = N_Parameter_Association then
               Other := Explicit_Actual_Parameter (P);
            else
               Other := P;
            end if;
            Find_Actual (Other, Other_Formal, Other_Call);
            Other_Is_Out := Ekind (Other_Formal) in
              E_Out_Parameter | E_In_Out_Parameter;
            pragma Assert (Call = Other_Call);

            if Actual = Other then
               --  We don't check against ourselves, but we do not
               --  when we have found ourselves, see below...
               Found_Myself := True;

            elsif not Found_Myself then
               --  We don't need to check B against A because we
               --  already would have checked A against B.
               null;

            elsif Is_Out or Other_Is_Out then
               --  We only check for aliasing if at least one of the
               --  parameters is an out paramter.
               Check_Node_Against_Node
                 (A => Actual,
                  B => Other,
                  A_Formal => Formal,
                  B_Formal => Other_Formal,
                  Introduces_Aliasing => Introduces_Aliasing);
            end if;

            P := Next (P);
         end loop;
      end;

      --  Check against globals.

      declare
         Reads  : Flow_Id_Sets.Set;
         Writes : Flow_Id_Sets.Set;
      begin
         Get_Globals (Subprogram => Entity (Name (Call)),
                      Reads      => Reads,
                      Writes     => Writes);
         if Is_Out then
            for R of Reads loop
               --  No use in checking both the read and the write of
               --  an in out global.
               if not Writes.Contains (Change_Variant (R, Out_View)) then
                  case R.Kind is
                     when Direct_Mapping =>
                        Check_Node_Against_Node
                          (A => Actual,
                           B => Get_Direct_Mapping_Id (R),
                           A_Formal => Formal,
                           B_Formal => Empty,
                           Introduces_Aliasing => Introduces_Aliasing);
                     when Magic_String =>
                        --  If we don't have a name for the global, by
                        --  definition we can't possibly reference it in a
                        --  parameter.
                        null;
                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
               end if;
            end loop;
         end if;
         for W of Writes loop
            case W.Kind is
               when Direct_Mapping =>
                  Check_Node_Against_Node
                    (A => Actual,
                     B => Get_Direct_Mapping_Id (W),
                     A_Formal => Formal,
                     B_Formal => Empty,
                     Introduces_Aliasing => Introduces_Aliasing);
               when Magic_String =>
                  --  If we don't have a name for the global, by
                  --  definition we can't possibly reference it in a
                  --  parameter.
                  null;
               when others =>
                  raise Why.Unexpected_Node;
            end case;
         end loop;
      end;

   end Check_Parameter_Against_Parameters_And_Globals;

   --------------------------
   -- Check_Procedure_Call --
   --------------------------

   procedure Check_Procedure_Call
     (N                   : Node_Id;
      Introduces_Aliasing : in out Boolean)
   is
   begin

      --  Check out and in out parameters against other parameters and
      --  globals.

      declare
         P      : Node_Id;
         Actual : Node_Id;
         Formal : Entity_Id;
         Call   : Node_Id;
      begin
         P := First (Parameter_Associations (N));
         while Present (P) loop
            if Nkind (P) = N_Parameter_Association then
               Actual := Explicit_Actual_Parameter (P);
            else
               Actual := P;
            end if;
            Find_Actual (Actual, Formal, Call);
            pragma Assert (Call = N);

            Check_Parameter_Against_Parameters_And_Globals
              (Actual,
               Introduces_Aliasing);

            P := Next (P);
         end loop;
      end;

      --  Check for aliasing between abstract state and computed
      --  globals.

   end Check_Procedure_Call;

end Flow.Antialiasing;
