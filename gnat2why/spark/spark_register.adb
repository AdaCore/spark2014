------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ R E G I S T E R                       --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                        Copyright (C) 2013-2017, AdaCore                  --
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
with Common_Containers;      use Common_Containers;
with Einfo;                  use Einfo;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;

package body SPARK_Register is

   -------------------------------
   -- Register_Compilation_Unit --
   -------------------------------

   procedure Register_Compilation_Unit (N : Node_Id) is

      function Process_Node (N : Node_Id) return Traverse_Result;
      --  Process a single node

      procedure Process_Tree is new Traverse_Proc (Process_Node);
      --  Recursively process an AST tree

      ------------------
      -- Process_Node --
      ------------------

      function Process_Node (N : Node_Id) return Traverse_Result is
         subtype Rewriten_Call is Node_Kind with
           Static_Predicate => Rewriten_Call in N_Block_Statement
                                              | N_Identifier
                                              | N_Null_Statement
                                              | N_Unchecked_Type_Conversion;
         --  Type with kinds of nodes that may represent rewritten subprogram
         --  calls.
         --  ??? this is quite subtle, perhaps we should just check the kind of
         --  the original node.

      begin
         --  First rewrite the node

         case Nkind (N) is
            --  Recursively call the tree rewriting procedure on subunits

            when N_Body_Stub =>
               Process_Tree (Unit (Library_Unit (N)));
               return OK;

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
                 Static_Predicate => N_Call in N_Subprogram_Call |
                                               N_Entry_Call_Statement;

            begin
               case Ekind (E) is
                  when Subprogram_Kind | Entry_Kind =>
                     case Nkind (Parent (N)) is
                        --  Register ordinary subprogram calls and internal
                        --  calls to protected subprograms and entries.
                        when N_Call =>
                           Register_Entity (E);

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
                           null;
                     end case;

                  when E_Constant
                     | E_Variable
                  =>
                     begin
                        case Nkind (Parent (E)) is
                           when N_Object_Declaration
                              | N_Iterator_Specification
                           =>
                              Register_Entity (E);

                           when others =>
                              null;
                        end case;
                     end;

                  when E_Abstract_State
                     | E_Loop_Parameter
                     | Formal_Kind
                  =>
                     Register_Entity (E);

                  when others =>
                     null;
               end case;
            end;
         end if;

         --  Explicitly traverse rewritten subprogram calls
         if Nkind (N) in Rewriten_Call
           and then Nkind (Original_Node (N)) in N_Subprogram_Call
         then
            Process_Tree (Original_Node (N));
         end if;

         --  Special-case type aspect subprograms
         --
         --  Default_Initial_Condition: expression is not part of the tree and
         --  thus needs to be explicitly traversed. The DIC procedure need not
         --  be registered, because the DIC expression either evaluates to true
         --  or raises an exception. None of these cause flow information (and
         --  that's why it is not registered in Direct_Calls).
         --
         --  Predicate: opposite of DIC, i.e. expression is traversed anyway
         --  and unlike DIC we need to register them, because when called in
         --  type memberhsip test it will affect the information flow (and
         --  that's why it is registered in Direct_Calls).

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

            --  We register type predicate functions unlike other subprograms,
            --  i.e. when they are declared and not when they are (implicitly)
            --  referenced.

            if Has_Predicates (N) then
               Register_Entity (Predicate_Function (N));
            end if;
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

                     when N_Access_To_Subprogram_Definition |
                          N_Entry_Body_Formal_Part          |
                          N_Entry_Declaration               =>
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

   --  Start of processing for Process_Node

   begin
      --  Skip generic units; care only about their instances

      if Is_Generic_Unit (Unique_Defining_Entity (N)) then
         null;

      --  This procedure is called on the declaration or body of a library unit
      --  (see spec of Sem.Walk_Library_Items), but we need here to process
      --  the parent of the compilation unit node when there is one, so that
      --  aspects rewritten as pragmas after the library unit declaration or
      --  body (listed in Pragmas_After) are also processed.

      elsif Present (Parent (N)) then
         Process_Tree (Parent (N));
      else
         Process_Tree (N);
      end if;
   end Register_Compilation_Unit;

end SPARK_Register;
