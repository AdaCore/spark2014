------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ R E G I S T E R                       --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2013-2019, AdaCore                     --
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

with Aspects;                use Aspects;
with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util;             use SPARK_Util;
with Stand;                  use Stand;

package body SPARK_Register is

   -------------------------------
   -- Register_Compilation_Unit --
   -------------------------------

   procedure Register_Compilation_Unit (N : Node_Id) is

      function Process_Node (N : Node_Id) return Traverse_Result;
      --  Process a single node

      procedure Process_Tree is
        new Traverse_More_Proc (Process_Node, Process_Itypes => True);
      --  Recursively process an AST tree

      ------------------
      -- Process_Node --
      ------------------

      function Process_Node (N : Node_Id) return Traverse_Result is
         subtype Rewriten_Call is Node_Kind with
           Static_Predicate => Rewriten_Call in N_Block_Statement
                                              | N_Identifier
                                              | N_Integer_Literal
                                              | N_Null_Statement
                                              | N_Qualified_Expression
                                              | N_Unchecked_Type_Conversion;
         --  Type with kinds of nodes that may represent rewritten subprogram
         --  calls.
         --  ??? this is quite subtle, perhaps we should just check the kind of
         --  the original node.

      begin
         --  Set the error location to advice the user on where the problem
         --  might be when this routine crash.

         Current_Error_Node := N;

         case Nkind (N) is
            --  Recursively call the tree rewriting procedure on subunits

            when N_Body_Stub =>
               if not Is_Generic_Unit (Unique_Defining_Entity (N)) then
                  Process_Tree (Unit (Library_Unit (N)));
               end if;

               return OK;

            when N_Generic_Declaration =>
               return Skip;

            when N_Package_Body
               | N_Subprogram_Body
            =>
               if Is_Generic_Unit (Unique_Defining_Entity (N)) then
                  return Skip;
               end if;

            --  Ignore freeze entities, because front end might not care to set
            --  all of their fields (such as Scope or Ekind).

            when N_Freeze_Entity =>
               return Skip;

            when others =>
               null;
         end case;

         --  Register any object/subprogram appearing in an expression, which
         --  comes from an object/subprogram declaration.

         if Nkind (N) in N_Has_Entity
           and then Present (Entity (N))
         then
            declare
               E : constant Entity_Id := Entity (N);

               subtype N_Call is Node_Kind with
                 Static_Predicate => N_Call in N_Subprogram_Call
                                             | N_Entry_Call_Statement;

            begin
               case Ekind (E) is
                  when Subprogram_Kind | Entry_Kind =>
                     case Nkind (Parent (N)) is
                        --  Register ordinary subprogram calls and internal
                        --  calls to protected subprograms and entries.
                        when N_Call =>

                           --  Ignore calls to predicate functions
                           if Ekind (E) = E_Function
                             and then Is_Predicate_Function (E)
                           then
                              null;
                           else
                              Register_Entity (E);
                           end if;

                        --  Register external calls to protected subprograms
                        --  and entries.
                        when N_Selected_Component =>
                           case Nkind (Parent (Parent (N))) is
                              when N_Call =>
                                 Register_Entity (E);

                              --  Register calls to entry families, internal
                              --  and external.
                              when N_Indexed_Component =>
                                 if Nkind (Parent (Parent (Parent (N)))) =
                                   N_Entry_Call_Statement
                                 then
                                    Register_Entity (E);
                                 end if;

                              when others =>
                                 null;
                           end case;

                        when Rewriten_Call =>
                           if Nkind (Original_Node (Parent (N))) in
                             N_Subprogram_Call
                           then
                              Register_Entity (E);
                           end if;

                        when others =>
                           if Is_Unchecked_Conversion_Instance (E) then
                              Register_Entity (E);
                           end if;
                     end case;

                  when E_Constant =>
                     Register_Entity (Unique_Entity (E));

                  when E_Variable =>
                     if Is_Quantified_Loop_Param (E) then
                        null;
                     else
                        Register_Entity (E);
                     end if;

                  when E_Loop_Parameter
                     | Formal_Kind
                  =>
                     Register_Entity (E);

                  when E_Abstract_State =>
                     Register_Entity
                       (if Present (Non_Limited_View (E))
                        then Non_Limited_View (E)
                        else E);

                  when others =>
                     null;
               end case;
            end;
         end if;

         --  Explicitly traverse rewritten subprogram calls and pragmas

         --  In particular, take care of pragma Debug, which is intentionally
         --  ignored by both flow a proof, but not-intentionally processed by
         --  front-end cross-references. In effect, if a subprogram is not in
         --  SPARK but has a pragma Debug, the call from that pragma will
         --  appear as its callee and must be resolved just like other calls.
         --  ??? this is a yet another reason for replacing front-end xrefs
         --  with something more precise and easier to control.
         if Nkind (N) in Rewriten_Call
           and then Nkind (Original_Node (N)) in N_Subprogram_Call
                                               | N_Pragma
                                               | N_Op
         then
            Process_Tree (Original_Node (N));
         end if;

         --  Aspect Address, unlike other aspects, it is not translated to
         --  a semantically-equivalent pragma, and like other aspects it is
         --  not attached to the tree. We need to explicitly traverse its
         --  expression, which may contain references to objects and calls
         --  to functions.
         if Nkind (N) in N_Object_Declaration
                       | N_Subprogram_Declaration
         then
            declare
               Address : constant Node_Id :=
                 Find_Aspect (Defining_Entity (N), Aspect_Address);
            begin
               if Present (Address) then
                  Process_Tree (Expression (Address));
               end if;
            end;
         end if;

         --  Special-case type aspect subprograms
         --
         --  Default_Initial_Condition: expression is not part of the tree and
         --  thus needs to be explicitly traversed. The DIC procedure need not
         --  be registered, because the DIC expression either evaluates to true
         --  or raises an exception. None of these cause flow information (and
         --  that's why it is not registered in Direct_Calls).
         --
         --  Predicate: expression is traversed anyway (because it is attached
         --  to the tree); just like DIC, it don't need to be registered,
         --  because it doesn't appear in Direct_Calls.

         if Nkind (N) in N_Entity
           and then Is_Type (N)
         then
            --  Only care about DIC of a base type (because derived types and
            --  subtypes just reuse the same expression and we want to repeat
            --  the work).

            if Has_Own_DIC (N)
              and then N = Base_Type (N)
            then
               declare
                  DIC_Proc : constant Node_Id := DIC_Procedure (N);

                  Expr : Node_Id;

               begin
                  --  Default_Initial_Condition may be given without any
                  --  expression, which means it defaults to True.
                  if Present (DIC_Proc) then
                     Expr := Get_Expr_From_Check_Only_Proc (DIC_Proc);

                     Process_Tree (Expr);
                  end if;
               end;
            end if;
         end if;

         --  Register dispatching operations, because they might be called only
         --  implicitly and we miss such calls in the above code.

         if Nkind (N) = N_Subprogram_Declaration then
            declare
               E : constant Entity_Id := Defining_Entity (N);

            begin
               if Is_Dispatching_Operation (E) then
                  Register_Entity (E);
               end if;
            end;
         end if;

         --  In many places we manipulate objects represented by names which is
         --  the only way to represent what comes from other compilation units.
         --  However, we often need to know what the name really represents,
         --  especially when looking from different contexts. To get this
         --  information we need a mapping from entity names to entity ids.
         --
         --  Here we register objects, loop parameters (but not in quantified
         --  expressions since nothing can be declared within them),
         --  discriminants, subprograms parameters (but not stub parameters
         --  since we essentially process stubs as if they would be ordinary
         --  definitions).
         --
         --  ??? this is quite delicate

         case Nkind (N) is
            when N_Loop_Parameter_Specification =>
               if Nkind (Parent (N)) /= N_Quantified_Expression then
                  Register_Entity (Defining_Entity (N));
               end if;

            when N_Discriminant_Specification
               | N_Object_Declaration
            =>
               Register_Entity (Defining_Entity (N));

            when N_Parameter_Specification =>
               declare
                  P : constant Node_Id := Parent (N);
               begin
                  case Nkind (P) is
                     when N_Subprogram_Specification =>
                        if Nkind (Parent (P)) /= N_Subprogram_Body_Stub then
                           Register_Entity (Defining_Entity (N));
                        end if;

                     when N_Entry_Declaration =>
                        Register_Entity (Defining_Entity (N));

                     --  Accept statements are not in SPARK, but for
                     --  completeness we register their parameters.

                     when N_Accept_Statement =>
                        Register_Entity (Defining_Entity (N));

                     when N_Access_To_Subprogram_Definition |
                          N_Entry_Body_Formal_Part          =>
                        null;

                     when others =>
                        raise Program_Error;
                  end case;
               end;

            when N_Package_Declaration        |
                 N_Protected_Type_Declaration |
                 N_Task_Type_Declaration      =>
               --  ??? is this needed for wrapper packages?
               Register_Entity (Defining_Entity (N));

            when others =>
               null;
         end case;

         return OK;
      end Process_Node;

   --  Start of processing for Register_Compilation_Unit

   begin
      --  Skip generic units; care only about their instances

      if Is_Generic_Unit (Unique_Defining_Entity (N)) then
         null;

      --  This procedure is called on the declaration or body of a library
      --  unit, but we also need to process the parent of the compilation unit
      --  node, so that aspects rewritten as pragmas after the library unit
      --  declaration or body (listed in Pragmas_After) are also processed.
      --  Only the Standard package has no such a parent.

      elsif N = Standard_Package_Node then
         Process_Tree (N);
      else
         Process_Tree (Parent (N));
      end if;

      --  Clear the error location (it will be set again by the next
      --  traverse-like routines).

      Current_Error_Node := Empty;
   end Register_Compilation_Unit;

end SPARK_Register;
