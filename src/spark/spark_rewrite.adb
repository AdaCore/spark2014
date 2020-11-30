------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S P A R K _ R E W R I T E                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2013-2020, AdaCore                     --
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
with Contracts;              use Contracts;
with Einfo;                  use Einfo;
with Flow.Dynamic_Memory;    use Flow.Dynamic_Memory;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Nmake;                  use Nmake;
with Sem_Aux;                use Sem_Aux;
with Sem_Eval;               use Sem_Eval;
with Sem_Prag;               use Sem_Prag;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with Stand;                  use Stand;
with Tbuild;                 use Tbuild;

package body SPARK_Rewrite is

   procedure Decorate_Unchecked_Deallocation (E : Entity_Id)
   with Pre => Is_Unchecked_Deallocation_Instance (E);
   --  Decorate Unchecked_Deallocation with this contract:
   --
   --     generic ...
   --     procedure Ada.Unchecked_Deallocation (X : in out Name) with
   --       Depends => (SPARK.Heap.Dynamic_Memory => SPARK.Heap.Dynamic_Memory,
   --                   X => null, null => X);
   --
   --  which cannot appear explicitly, because we can't reference a custom unit
   --  like SPARK.Heap in a predefined unit like Ada.Unchecked_Deallocation.
   --
   --  Note: decorating it here feels like a hack, but the alternative would
   --  be to special-case all routines that examine the Depends contract, which
   --  seems much more error-prone.

   procedure Rewrite_Call (N : Node_Id);
   --  Replace instantiations of unchecked conversions with
   --  N_Unchecked_Type_Conversion nodes.

   procedure Rewrite_Fixed_Point_Mult_Div (N : Node_Id);
   --  Rewrite the type conversion introduced on multiplication/division
   --  between fixed-point values, to avoid the use of the universal-fixed
   --  type used by the compiler as an overload resolution trick.

   procedure Rewrite_Subprogram_Instantiation (N : Node_Id)
   with Pre => Nkind (N) in N_Subprogram_Instantiation;
   --  Replace names in instances of generic subprograms with names of
   --  the original subprograms; we prefer the original names when outputting
   --  error messages and generating Why code. Also, decorate instances of
   --  Ada.Unchecked_Deallocation.

   procedure Rewrite_Subprogram_Reference (N : Node_Id);
   --  Replace renamings and inherited subprograms by the subprogram they
   --  rename or inherit.

   procedure Rewrite_Wrapper_Package (N : Node_Id)
   with Pre => Nkind (N) = N_Package_Declaration;
   --  Wrapper packages typically have unique names with the GP suffix, except
   --  those which themselves are compilation units, because apparently this
   --  makes the name resolution easier (see Analyze_Instance_And_Renamings for
   --  details). Here we add such a suffix to make their name unique.

   procedure Rewrite_Real_Literal (N : Node_Id);
   --  Rewrite real literals that are not sub-expressions of static expressions
   --  into machine numbers, when the frontend has not done so already as part
   --  of Eval_Real_Literal. This can only be performed here and not as part
   --  of evaluation or expansion in the frontend, because the information that
   --  the parent expression is static is only available after the real literal
   --  node has been evaluated and expanded.

   -------------------------------------
   -- Decorate_Unchecked_Deallocation --
   -------------------------------------

   procedure Decorate_Unchecked_Deallocation (E : Entity_Id) is
      function Make_Identifier (E : Entity_Id) return Node_Id;

      ---------------------
      -- Make_Identifier --
      ---------------------

      function Make_Identifier (E : Entity_Id) return Node_Id is
         N : constant Node_Id :=
           Make_Identifier
             (Sloc => No_Location, Chars => Chars (E));
      begin
         Set_Entity (N, E);
         return N;
      end Make_Identifier;

      --  Local variables

      Spec : constant Node_Id := Subprogram_Spec (E);
      --  Spec of the instance procedure; its Sloc will be used as a Sloc for
      --  the pragma Depends (it could be used as a Sloc for nodes of the
      --  pragma argument association, but they are never examined).

      Prag : constant Node_Id :=
        Make_Pragma
          (Sloc                         => Sloc (Spec),
           Pragma_Argument_Associations =>
             New_List
               (Make_Pragma_Argument_Association
                  (Sloc       => No_Location,
                   Expression =>
                     Make_Aggregate
                       (Sloc                     => No_Location,
                        Component_Associations   =>
                          (New_List
                             (Make_Component_Association
                                (Sloc       => No_Location,
                                 Choices    =>
                                   New_List
                                     (Make_Identifier (Heap_State)),
                                 Expression =>
                                   Make_Identifier (Heap_State)),
                              Make_Component_Association
                                (Sloc       => No_Location,
                                 Choices    =>
                                   New_List
                                     (Make_Identifier (First_Formal (E))),
                                 Expression =>
                                   Make_Null (No_Location)),
                              Make_Component_Association
                                (Sloc       => No_Location,
                                 Choices    =>
                                   New_List (Make_Null (No_Location)),
                                 Expression =>
                                   Make_Identifier (First_Formal (E)))))))),
           Pragma_Identifier            =>
             Make_Identifier (No_Location, Name_Depends));

   --  Start of processing for Decorate_Unchecked_Deallocation

   begin
      --  This appears to be minimal anchoring of the pragma to the AST
      Insert_After (Spec, Prag);
      Add_Contract_Item (Prag, E);

      --  Apply some sanity-checks
      pragma Assert
        (Present (Find_Contract (E, Pragma_Depends)));
      pragma Assert
        (Defining_Entity (Find_Related_Declaration_Or_Body (Prag)) = E);

   end Decorate_Unchecked_Deallocation;

   ------------------
   -- Rewrite_Call --
   ------------------

   procedure Rewrite_Call (N : Node_Id) is
      Nam : constant Node_Id := Name (N);
   begin
      --  If the subprogram is actually an unchecked type conversion we
      --  rewrite the tree to use an N_Unchecked_Type_Conversion node
      --  instead, as documented in Sinfo. The original call to an instance
      --  of Unchecked_Conversion is still accessible in the tree as the
      --  Original_Node of the new N_Unchecked_Type_Conversion node. We mark
      --  the node N_Unchecked_Type_Conversion as coming from source so that
      --  it can be distinguished from compiler-generated unchecked type
      --  conversion nodes, which are translated differently into Why.

      if Is_Entity_Name (Nam)
        and then Is_Unchecked_Conversion_Instance (Entity (Nam))
      then
         --  Rewrite the subprogram name as it will be used in the translation
         --  to Why3.

         Rewrite_Subprogram_Reference (Nam);

         Rewrite (Old_Node => N,
                  New_Node => Unchecked_Convert_To
                    (Typ  => Etype (Etype (N)),
                     Expr => First_Actual (N)));
         Set_Comes_From_Source (N, True);

         --  Reset correct parent of original node, as this may be used
         --  during the translation to Why.

         Set_Parent (Original_Node (N), Parent (N));
      end if;
   end Rewrite_Call;

   ----------------------------------
   -- Rewrite_Fixed_Point_Mult_Div --
   ----------------------------------

   procedure Rewrite_Fixed_Point_Mult_Div (N : Node_Id) is
      Expr : constant Node_Id := Expression (N);
      Typ  : constant Entity_Id := Etype (N);
   begin
      Set_Etype (Expr, Typ);
   end Rewrite_Fixed_Point_Mult_Div;

   --------------------------
   -- Rewrite_Real_Literal --
   --------------------------

   --  Only rewrite real literals that are sub-expressions (otherwise frontend
   --  has already converted them to machine numbers) and not part of a static
   --  expression, as it is allowed for a literal sub-expression to be outside
   --  the bounds of the expression type in a static expression. For an example
   --  where this is needed, see definition of Forever in g-socket.ads. In such
   --  a case, GNATprove will use the value computed by the frontend for the
   --  static expression when in bounds, otherwise an error should have been
   --  emitted.

   --  Also ignore unanalyzed nodes without Etype, as these correspond to parts
   --  of the AST that should not be used in GNATprove, typically values under
   --  Associated_Node or Generic_Associations.

   procedure Rewrite_Real_Literal (N : Node_Id) is
      Par : constant Node_Id := Parent (N);
   begin
      if Nkind (Par) in N_Subexpr
        and then not Is_Static_Expression (Par)
        and then Present (Etype (N))
      then
         Check_Non_Static_Context (N);
      end if;
   end Rewrite_Real_Literal;

   --------------------------------------
   -- Rewrite_Subprogram_Instantiation --
   --------------------------------------

   procedure Rewrite_Subprogram_Instantiation (N : Node_Id) is

      function Wrapped_Instance (Wrapper_Package : Entity_Id) return Entity_Id
      with Pre  => Is_Wrapper_Package (Wrapper_Package),
           Post => Ekind (Wrapped_Instance'Result) in E_Function | E_Procedure;
      --  Returns entity of the wrapped instance

      ----------------------
      -- Wrapped_Instance --
      ----------------------

      function Wrapped_Instance
        (Wrapper_Package : Entity_Id)
         return Entity_Id
      is
         E : Entity_Id;
      begin
         --  The first/next entity chain of a generic subprogram instance
         --  contains all generic formal parameters, followed by the
         --  subprogram declaration. Go directly to that declaration by
         --  skipping the formal part.
         E := First_Entity (Wrapper_Package);

         loop
            pragma Loop_Invariant (Present (E));

            if Ekind (E) in E_Function | E_Procedure
              and then not Is_Generic_Actual_Subprogram (E)
            then
               return E;
            end if;

            Next_Entity (E);
         end loop;
      end Wrapped_Instance;

      --  Local variables

      Wrapper_Package : constant Entity_Id :=
        Defining_Entity (Instance_Spec (N));

      Subprogram_Instance : constant Entity_Id :=
        Wrapped_Instance (Wrapper_Package);

      Orig_Name_Id : constant Name_Id := Chars (Defining_Unit_Name (N));
      --  ??? how about homonyms?

   --  Start of processing for Rewrite_Subprogram_Instantiation

   begin
      Set_Chars (Subprogram_Instance, Orig_Name_Id);

      if Is_Unchecked_Deallocation_Instance (Subprogram_Instance) then
         Decorate_Unchecked_Deallocation (Subprogram_Instance);
      end if;
   end Rewrite_Subprogram_Instantiation;

   ----------------------------------
   -- Rewrite_Subprogram_Reference --
   ----------------------------------

   procedure Rewrite_Subprogram_Reference (N : Node_Id) is
      E : constant Entity_Id := Entity (N);
   begin
      --  If the subprogram is a renaming or an inherited primitive operation,
      --  replace it with the name of the actual subprogram being
      --  called. Both have an Alias component, that points to the immediate
      --  renamed or inherited subprogram. The Ultimate_Alias function
      --  retrieves the last subprogram in a chain of aliases. Note that
      --  renamings and inherited primitive operations can be distinguished
      --  by the kind of their parent node: the entity for a renaming has
      --  the function or procedure specification node as parent, while an
      --  inherited primitive operation has the derived type declaration as
      --  parent.

      if (Is_Overloadable (E) or else Ekind (E) = E_Subprogram_Type)
        and then Present (Alias (E))
      then
         Set_Entity (N, Ultimate_Alias (E));
      end if;
   end Rewrite_Subprogram_Reference;

   -----------------------------
   -- Rewrite_Wrapper_Package --
   -----------------------------

   procedure Rewrite_Wrapper_Package (N : Node_Id) is
      Def_Ent : constant Entity_Id := Defining_Entity (N);

   begin
      if Is_Wrapper_Package (Def_Ent)
        and then Is_Compilation_Unit (Def_Ent)
      then
         --  Add a suffix just like in Analyze_Instance_And_Renamings

         Set_Chars (Def_Ent,
                    New_External_Name
                      (Related_Id   => Chars (Def_Ent),
                       Suffix       => "GP",
                       Suffix_Index => Source_Offset (Sloc (Def_Ent))));

         --  ??? we could add the same suffix to package body, but apparently
         --  there is no need for that.
      end if;
   end Rewrite_Wrapper_Package;

   ------------------------------
   -- Rewrite_Compilation_Unit --
   ------------------------------

   procedure Rewrite_Compilation_Unit (N : Node_Id) is

      function Rewrite_Node (N : Node_Id) return Traverse_Result;
      --  Apply expansion operations on a node

      procedure Rewrite_Nodes is
        new Traverse_More_Proc (Rewrite_Node, Process_Itypes => True);

      ------------------
      -- Rewrite_Node --
      ------------------

      function Rewrite_Node (N : Node_Id) return Traverse_Result is
         subtype Rewriten_Call is Node_Kind with
           Static_Predicate => Rewriten_Call in N_Block_Statement
                                              | N_Identifier
                                              | N_Integer_Literal
                                              | N_Null_Statement
                                              | N_Qualified_Expression
                                              | N_Unchecked_Type_Conversion;
         --  ??? this is copy-pasted from SPARK_Register; refactor

      begin
         --  Explicitly traverse rewritten subprogram calls and pragmas (e.g.
         --  pragma Debug).
         if Nkind (N) in Rewriten_Call
           and then Nkind (Original_Node (N)) in N_Subprogram_Call
                                               | N_Pragma
                                               | N_Op
         then
            Rewrite_Nodes (Original_Node (N));
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
                  Rewrite_Nodes (Expression (Address));
               end if;
            end;
         end if;

         case Nkind (N) is
            when N_Real_Literal =>
               Rewrite_Real_Literal (N);

            --  The multiplication and division operations on fixed-point
            --  types have a return type of universal_fixed (with no bounds),
            --  which is used as an overload resolution trick to allow
            --  free conversion between certain real types on the result of
            --  multiplication or division. The target non-universal type
            --  determines the actual sort of multiplication or division
            --  performed, and therefore determines the possibility of
            --  overflow. In the compiler, the multiplication is expanded so
            --  the operands are first converted to some common type, so back
            --  ends don't see the universal_fixed Etype. Here, we are seeing
            --  the unexpanded operation because we are running in a mode that
            --  disables the expansion. Hence, we recognize the universal_fixed
            --  case specially and in that case rewrite the AST to avoid the
            --  conversion, by directly using the target type of the enclosing
            --  conversion as the type of the multiplication or division.

            when N_Type_Conversion =>
               declare
                  Expr : constant Node_Id := Expression (N);
               begin
                  if Nkind (Expr) in N_Op_Multiply | N_Op_Divide
                    and then Etype (Expr) = Universal_Fixed
                  then
                     Rewrite_Fixed_Point_Mult_Div (N);
                  end if;
               end;

            --  Replace calls to Unchecked_Conversion instances by nodes
            --  N_Unchecked_Type_Conversion, which are marked as coming
            --  from source.

            when N_Function_Call =>
               Rewrite_Call (N);

            --  Replace renamings and inherited subprograms by the subprogram
            --  they rename or inherit.

            when N_Identifier
               | N_Expanded_Name
               | N_Operator_Symbol
            =>
               if Present (Entity (N))
                 and then Is_Subprogram (Entity (N))
               then
                  Rewrite_Subprogram_Reference (N);
               end if;

            when N_Subprogram_Instantiation =>
               Rewrite_Subprogram_Instantiation (N);

            when N_Package_Declaration =>
               Rewrite_Wrapper_Package (N);

            --  Recursively call the tree rewriting procedure on subunits

            when N_Body_Stub =>
               if not Is_Generic_Unit (Unique_Defining_Entity (N)) then
                  Rewrite_Nodes (Unit (Library_Unit (N)));
               end if;

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

            --  Traverse expressions for DIC procedures

            when N_Full_Type_Declaration =>
               if Comes_From_Source (N) then
                  declare
                     Ty       : constant Entity_Id := Defining_Entity (N);
                     Inv_Proc : constant Entity_Id := Invariant_Procedure (Ty);
                     Inv_Expr : Node_Id;
                     DIC_Proc : Entity_Id;
                     DIC_Expr : Node_Id;

                  begin
                     --  ??? The following is slighly different from
                     --  SPARK_Register; both should be unified.

                     if Present (Inv_Proc) then
                        Inv_Expr := Get_Expr_From_Check_Only_Proc (Inv_Proc);

                        if Present (Inv_Expr) then
                           Rewrite_Nodes (Inv_Expr);

                        --  If the invariant procedure has no expression then
                        --  it calls the partial invariant procedure, so get
                        --  the expression from there. (Such partial invariant
                        --  procedures come from Type_Invariant on a private
                        --  part, which as of today is not allowed in SPARK,
                        --  but it is better to traverse it anyway.)

                        else
                           Inv_Expr :=
                             Get_Expr_From_Check_Only_Proc
                               (Partial_Invariant_Procedure (Ty));

                           pragma Assert (Present (Inv_Expr));

                           Rewrite_Nodes (Inv_Expr);
                        end if;
                     end if;

                     if Has_Own_DIC (Ty) then
                        DIC_Proc := Partial_DIC_Procedure (Ty);

                        if Present (DIC_Proc) then
                           DIC_Expr :=
                             Get_Expr_From_Check_Only_Proc (DIC_Proc);

                           if Present (DIC_Expr) then
                              Rewrite_Nodes (DIC_Expr);
                           end if;
                        end if;
                     end if;
                  end;
               end if;

            when others =>
               null;
         end case;

         return OK;
      end Rewrite_Node;

   --   Start of processing for Rewrite_Compilation_Unit

   begin
      --  Avoid rewriting generic units which are only preanalyzed, which may
      --  cause rewriting to fail, as this is not needed.

      if Is_Generic_Unit (Unique_Defining_Entity (N)) then
         null;

      --  This procedure is called on the declaration or body of a library
      --  unit, but we also need to process the parent of the compilation unit
      --  node, so that aspects rewritten as pragmas after the library unit
      --  declaration or body (listed in Pragmas_After) are also processed.
      --  Only the Standard package has no such a parent.

      elsif N = Standard_Package_Node then
         pragma Assert (No (Parent (N)));
         Rewrite_Nodes (N);
      else
         pragma Assert (Nkind (Parent (N)) = N_Compilation_Unit);
         Rewrite_Nodes (Parent (N));
      end if;
   end Rewrite_Compilation_Unit;

end SPARK_Rewrite;
