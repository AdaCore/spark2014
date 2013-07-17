------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Sinfo;                  use Sinfo;
with Uintp;                  use Uintp;

with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;

with Why.Atree.Builders;     use Why.Atree.Builders;

package body Gnat2Why.Util is

   -------------------------------------
   -- Expression_Depends_On_Variables --
   -------------------------------------

   function Expression_Depends_On_Variables (N : Node_Id) return Boolean is

      Variable_Reference_Seen : Boolean := False;

      function Is_Variable_Reference (N : Node_Id) return Traverse_Result;
      --  Attempt to find a variable reference in N

      procedure Search_Variable_Reference is
        new Traverse_Proc (Is_Variable_Reference);

      ---------------------------
      -- Is_Variable_Reference --
      ---------------------------

      function Is_Variable_Reference (N : Node_Id) return Traverse_Result is
      begin
         if Nkind_In (N, N_Identifier, N_Expanded_Name)
           and then Present (Entity (N))
           and then (case Ekind (Entity (N)) is
                        when Object_Kind     => Is_Mutable_In_Why (Entity (N)),
                        when Subprogram_Kind => Has_Global_Reads (Entity (N)),
                        when others          => False)
         then
            Variable_Reference_Seen := True;
            return Abandon;

         --  Continue the traversal

         else
            return OK;
         end if;
      end Is_Variable_Reference;

   begin
      Search_Variable_Reference (N);
      return Variable_Reference_Seen;
   end Expression_Depends_On_Variables;

   -------------------------
   -- Create_Zero_Binding --
   -------------------------

   function Create_Zero_Binding
     (Vars : Node_Lists.List;
      Prog : W_Prog_Id) return W_Prog_Id
   is
      Result   : W_Prog_Id;
   begin
      Result := Prog;
      for V of Vars loop
         Result :=
           New_Binding_Ref (Name     => W_Identifier_Id (V),
                            Def      => New_Integer_Constant (Value => Uint_0),
                            Context  => Result);
      end loop;
      return Result;
   end Create_Zero_Binding;

   -----------------------
   -- Is_Mutable_In_Why --
   -----------------------

   function Is_Mutable_In_Why (N : Node_Id) return Boolean is
   begin
      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression).

      if Ekind (N) = E_Loop_Parameter then
         return not (Is_Quantified_Loop_Param (N));

      --  A component or discriminant is not separately considered as mutable,
      --  only the enclosing object is. This ensures that components used in
      --  the named notation of aggregates are not considered as references
      --  to mutable variables (e.g. in Expression_Depends_On_Variables).

      elsif Ekind (N) in E_Enumeration_Literal |
                         E_Component           |
                         E_Discriminant        |
                         Named_Kind            |
                         Subprogram_Kind
              or else
            Is_Constant_Object (N)
      then
         return False;

      else
         return True;
      end if;
   end Is_Mutable_In_Why;

end Gnat2Why.Util;
