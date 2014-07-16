------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S P A R K _ R E W R I T E                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                        Copyright (C) 2013-2014, AdaCore                  --
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
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Aux;                use Sem_Aux;
with Sem_Eval;               use Sem_Eval;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Snames;                 use Snames;
with Tbuild;                 use Tbuild;

with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;

package body SPARK_Rewrite is

   procedure Rewrite_Call (N : Node_Id);
   --  Replace renamings and inherited subprograms by the subprogram they
   --  rename or inherit.
   --
   --  Replace instantiations of unchecked conversions with
   --  N_Unchecked_Type_Conversion nodes.

   procedure Rewrite_Identifier (N : Node_Id);
   --  Replace identifiers by their compile-time known constant value when
   --  possible.

   ------------------
   -- Rewrite_Call --
   ------------------

   procedure Rewrite_Call (N : Node_Id) is
   begin
      --  If the subprogram is a renaming or an inherited primitive operation,
      --  replace it in the call with the name of the actual subprogram being
      --  called. Both have an Alias component, that points to the immediate
      --  renamed or inherited subprogram. The Ultimate_Alias function
      --  retrieves the last subprogram in a chain of aliases. Note that
      --  renamings and inherited primitive operations can be distinguished
      --  by the kind of their parent node: the entity for a renaming has
      --  the function or procedure specification node as parent, while an
      --  inherited primitive operation has the derived type declaration as
      --  parent.

      if Nkind (Name (N)) in N_Has_Entity
        and then Present (Entity (Name (N)))
      then
         declare
            E : constant Entity_Id := Entity (Name (N));
         begin
            if (Is_Overloadable (E) or else Ekind (E) = E_Subprogram_Type)
              and then Present (Alias (E))
            then
               Set_Entity (Name (N), Ultimate_Alias (E));
            end if;
         end;
      end if;

      --  If the subprogram is actually an unchecked type conversion we
      --  rewrite the tree to use an N_Unchecked_Type_Conversion node
      --  instead, as documented in Sinfo. The original call to an instance
      --  of Unchecked_Conversion is still accessible in the tree as the
      --  Original_Node of the new N_Unchecked_Type_Conversion node. We mark
      --  the node N_Unchecked_Type_Conversion as coming from source so that
      --  it can be distinguished from compiler-generated unchecked type
      --  conversion nodes, which are translated differently into Why.

      if Nkind (Name (N)) in N_Has_Entity
        and then Present (Entity (Name (N)))
        and then Is_Intrinsic_Subprogram (Entity (Name (N)))
      then
         declare
            E   : constant Entity_Id := Entity (Name (N));
            Nam : Name_Id;
         begin
            if Present (Parent (E))
              and then Present (Generic_Parent (Parent (E)))
            then
               Nam := Chars (Generic_Parent (Parent (E)));
            else
               Nam := Chars (E);
            end if;

            if Nam = Name_Unchecked_Conversion then
               Rewrite (Old_Node => N,
                        New_Node => Unchecked_Convert_To
                          (Typ  => Etype (Etype (N)),
                           Expr => First (Parameter_Associations (N))));
               Set_Comes_From_Source (N, True);

               --  Reset correct parent of original node, as this may be used
               --  during the translation to Why.

               Set_Parent (Original_Node (N), Parent (N));
            end if;
         end;
      end if;
   end Rewrite_Call;

   ------------------------
   -- Rewrite_Identifier --
   ------------------------

   --  The frontend performs only some constant folding, for example it does
   --  not constant-fold real literals inside non-constant expressions. Perform
   --  it here, to avoid generating unprovable VCs due to the translation of
   --  constants, for example constants of fixed-point types.

   procedure Rewrite_Identifier (N : Node_Id) is
   begin
      if Present (Entity (N))
        and then Ekind (Entity (N)) = E_Constant
      then
         declare
            Const_Expr : constant Node_Id := Constant_Value (Entity (N));
         begin
            if Present (Const_Expr)
              and then Compile_Time_Known_Value (Const_Expr)
            then
               if Is_Integer_Type (Etype (N)) then
                  Fold_Uint (N, Expr_Value (Const_Expr),
                             Is_Static_Expression (N));
               elsif Is_Real_Type (Etype (N)) then
                  Fold_Ureal (N, Expr_Value_R (Const_Expr),
                              Is_Static_Expression (N));
               end if;
            end if;
         end;
      end if;
   end Rewrite_Identifier;

   ------------------------------
   -- Rewrite_Compilation_Unit --
   ------------------------------

   procedure Rewrite_Compilation_Unit (N : Node_Id) is

      function Rewrite_Node (N : Node_Id) return Traverse_Result;
      --  Apply expansion operations on a node

      procedure Rewrite_Nodes is
        new Traverse_Proc (Rewrite_Node);

      ------------------
      -- Rewrite_Node --
      ------------------

      function Rewrite_Node (N : Node_Id) return Traverse_Result is
      begin
         --  Register any object/subprogram appearing in an expression, which
         --  comes from an object/subprogram declaration.

         if Nkind (N) in N_Has_Entity
           and then Nkind (Entity (N)) in N_Entity
         then
            declare
               E : constant Entity_Id := Entity (N);
            begin
               case Ekind (E) is
                  when Subprogram_Kind =>
                     begin
                        case Nkind (Parent (Parent (E))) is
                           when N_Subprogram_Body        |
                                N_Subprogram_Declaration =>
                              Register_Entity (E);

                           when others =>
                              null;
                        end case;
                     end;

                  when E_Constant |
                       E_Variable =>
                     begin
                        case Nkind (Parent (E)) is
                           when N_Object_Declaration     |
                                N_Iterator_Specification =>
                              Register_Entity (E);

                           when others =>
                              null;
                        end case;
                     end;

                  when E_Abstract_State |
                       E_Loop_Parameter |
                       Formal_Kind      =>
                     Register_Entity (E);

                  when others =>
                     null;
               end case;
            end;
         end if;

         --  In some cases, an object still needs to be registered although
         --  it does not appear in an expression. This is the case for example
         --  for a formal generic constant parameter which is simplified out in
         --  the generic instance. It may still appear in the effects for the
         --  instance, and as such should be registered.

         if Nkind (N) = N_Object_Declaration then
            Register_Entity (Defining_Entity (N));
         end if;

         case Nkind (N) is
            when N_Identifier | N_Expanded_Name =>
               Rewrite_Identifier (N);

            when N_Subprogram_Call =>
               Rewrite_Call (N);

            --  Recursively call the tree rewriting procedure on subunits

            when N_Body_Stub =>
               Rewrite_Nodes (Unit (Library_Unit (N)));

            when others =>
               null;
         end case;
         return OK;
      end Rewrite_Node;

   --   Start of Rewrite_Compilation_Unit

   begin
      --  Rewrite_Compilation_Unit is called on the declaration or body of a
      --  library unit (see spec of Sem.Walk_Library_Items), but we need here
      --  to call Rewrite_Nodes on the parent compilation unit node when there
      --  is one, so that aspects rewritten as pragmas after the library unit
      --  declaration or body (listed in Pragmas_After) are also rewritten.

      if Present (Parent (N)) then
         Rewrite_Nodes (Parent (N));
      else
         Rewrite_Nodes (N);
      end if;
   end Rewrite_Compilation_Unit;

end SPARK_Rewrite;
