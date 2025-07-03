------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S P A R K _ R E W R I T E                        --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2013-2025, AdaCore                     --
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

with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Aspects;                use Aspects;
with Atree;                  use Atree;
with Einfo.Entities;         use Einfo.Entities;
with Einfo.Utils;            use Einfo.Utils;
with Exp_Attr;               use Exp_Attr;
with Flow_Error_Messages;
with Gnat2Why_Args;
with Namet;                  use Namet;
with Nlists;
with Nmake;
with Sem_Aux;                use Sem_Aux;
with Sem_Eval;               use Sem_Eval;
with Sem_Util;               use Sem_Util;
with Sinfo.Nodes;            use Sinfo.Nodes;
with Sinfo.Utils;            use Sinfo.Utils;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with Stand;                  use Stand;
with Tbuild;                 use Tbuild;

package body SPARK_Rewrite is

   procedure Rewrite_Null_Procedure (N : N_Subprogram_Declaration_Id);
   --  Rewrite a null procedure into an equivalent procedure body. We are doing
   --  it here to avoid interfering with freezing in the frontend, as a null
   --  procedure declaration does not cause freezing, while a procedure body
   --  does.
   --
   --  Note that Sem_Ch6.Analyze_Null_Procedure already rewrites null procedure
   --  declarations as procedure bodies when they act as completion, so N here
   --  cannot be a completion.

   procedure Rewrite_Old_Attribute (N : Node_Id);
   --  Set the Etype of references to the Old attribute to the Etype of their
   --  prefix. If the prefix's type is a constrained Itype, use its base type
   --  instead to avoid leaking references to variables outside the Old
   --  attribute.

   procedure Rewrite_Subprogram_Instantiation (N : Node_Id)
   with Pre => Nkind (N) in N_Subprogram_Instantiation;
   --  Replace names in instances of generic subprograms with names of
   --  the original subprograms; we prefer the original names when outputting
   --  error messages and generating Why code.

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

   ----------------------------
   -- Rewrite_Null_Procedure --
   ----------------------------

   procedure Rewrite_Null_Procedure (N : N_Subprogram_Declaration_Id) is
      Loc  : constant Source_Ptr := Sloc (N);
      Spec : constant Node_Id := Specification (N);
      Subp : constant Entity_Id := Defining_Entity (Spec);

      Form      : Node_Id;
      Subp_Body : Entity_Id;
      Null_Stmt : constant Node_Id := Nmake.Make_Null_Statement (Loc);
      Null_Body : constant Node_Id :=
        Nmake.Make_Subprogram_Body
          (Loc,
           Specification              => New_Copy_Tree (Spec),
           Declarations               => Nlists.New_List,
           Handled_Statement_Sequence =>
             Nmake.Make_Handled_Sequence_Of_Statements
               (Loc, Statements => Nlists.New_List (Null_Stmt)));
   begin
      Set_Corresponding_Spec (Null_Body, Subp);

      --  Create new entities for body and formals

      Subp_Body := Nmake.Make_Defining_Identifier (Sloc (Subp), Chars (Subp));
      Mutate_Ekind (Subp_Body, E_Subprogram_Body);
      Set_Etype (Subp_Body, Etype (Defining_Entity (N)));
      Set_Defining_Unit_Name (Specification (Null_Body), Subp_Body);
      Set_Scope (Subp_Body, Scope (Subp));
      Set_SPARK_Pragma (Subp_Body, SPARK_Pragma (Subp));

      Form :=
        Nlists.First (Parameter_Specifications (Specification (Null_Body)));
      while Present (Form) loop
         declare
            Param     : constant Entity_Id := Defining_Identifier (Form);
            New_Param : constant Entity_Id :=
              Nmake.Make_Defining_Identifier (Sloc (Param), Chars (Param));
         begin
            Mutate_Ekind (New_Param, Ekind (Param));
            Set_Etype (New_Param, Etype (Param));
            Set_Defining_Identifier (Form, New_Param);
            Set_Scope (New_Param, Subp);
            Nlists.Next (Form);
         end;
      end loop;

      Set_Corresponding_Body (N, Subp_Body);
      Set_Null_Present (Specification (N), False);
      Nlists.Insert_After (N, Null_Body);
   end Rewrite_Null_Procedure;

   ---------------------------
   -- Rewrite_Old_Attribute --
   ---------------------------

   procedure Rewrite_Old_Attribute (N : Node_Id) is
      Pref : constant Node_Id := Prefix (N);
      Typ  : Entity_Id := Etype (Pref);

   begin
      --  For constrained Itypes, use the base type to avoid leaking references
      --  to the pre-state outside of the Old attribute.

      if Is_Itype (Typ)
        and then Is_Composite_Type (Typ)
        and then Is_Constrained (Typ)
        and then not Is_Constrained (Base_Type (Typ))
      then
         Typ := Base_Type (Typ);
      end if;

      Set_Etype (N, Typ);
   end Rewrite_Old_Attribute;

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
      with
        Pre  => Is_Wrapper_Package (Wrapper_Package),
        Post => Ekind (Wrapped_Instance'Result) in E_Function | E_Procedure;
      --  Returns entity of the wrapped instance

      ----------------------
      -- Wrapped_Instance --
      ----------------------

      function Wrapped_Instance (Wrapper_Package : Entity_Id) return Entity_Id
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

      if Present (E)
        and then (Is_Overloadable (E) or else Ekind (E) = E_Subprogram_Type)
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
      if Is_Wrapper_Package (Def_Ent) and then Is_Compilation_Unit (Def_Ent)
      then
         --  Add a suffix just like in Analyze_Instance_And_Renamings

         Set_Chars
           (Def_Ent,
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

      procedure Rewrite_Aspect (E : Entity_Id; A : Aspect_Id);
      --  Apply expansion operations on the expression of aspect A of E if any
      --  and to its corresponding representation item, if any.

      function Rewrite_Node (N : Node_Id) return Traverse_Result;
      --  Apply expansion operations on a node

      procedure Rewrite_Nodes is new
        Traverse_More_Proc (Rewrite_Node, Process_Itypes => True);

      --------------------
      -- Rewrite_Aspect --
      --------------------

      procedure Rewrite_Aspect (E : Entity_Id; A : Aspect_Id) is
         Aspect_Node : constant Node_Id := Find_Aspect (E, A);
         Rep_Item    : Node_Id;
      begin
         if Present (Aspect_Node) then
            Rewrite_Nodes (Expression (Aspect_Node));
            Rep_Item := Aspect_Rep_Item (Aspect_Node);
            if Nkind (Rep_Item) = N_Attribute_Definition_Clause then
               Rewrite_Nodes (Expression (Rep_Item));
            end if;
         end if;
      end Rewrite_Aspect;

      ------------------
      -- Rewrite_Node --
      ------------------

      function Rewrite_Node (N : Node_Id) return Traverse_Result is
         subtype Rewriten_Call is Node_Kind
         with
           Static_Predicate =>
             Rewriten_Call
             in N_Block_Statement
              | N_Identifier
              | N_Integer_Literal
              | N_Null_Statement
              | N_Qualified_Expression;
         --  ??? this is copy-pasted from SPARK_Register; refactor

      begin
         --  Set error node so that bugbox information will be correct

         Current_Error_Node := N;

         --  Delete lines of code passed through the --exclude-line switch, by
         --  rewriting the declaration, statement or pragma into a call marker
         --  node which is ignored by gnat2why.

         if Gnat2Why_Args.Exclude_Line /= Null_Unbounded_String
           and then Nkind (N)
                    in N_Declaration
                     | N_Later_Decl_Item
                     | N_Statement_Other_Than_Procedure_Call
                     | N_Procedure_Call_Statement
                     | N_Pragma
           and then Flow_Error_Messages.Is_Excluded_Line (Sloc (N))
         then
            Rewrite (N, Nmake.Make_Call_Marker (Sloc (N)));
         end if;

         --  Explicitly traverse rewritten subprogram calls and pragmas (e.g.
         --  pragma Debug).
         if Nkind (N) in Rewriten_Call
           and then Nkind (Original_Node (N))
                    in N_Subprogram_Call | N_Pragma | N_Op
         then
            Rewrite_Nodes (Original_Node (N));
         end if;

         --  Aspect Address, unlike other aspects, it is not translated to
         --  a semantically-equivalent pragma, and like other aspects it is
         --  not attached to the tree. We need to explicitly traverse its
         --  expression, which may contain references to objects and calls
         --  to functions.
         if Nkind (N) in N_Object_Declaration | N_Subprogram_Declaration then
            Rewrite_Aspect (Defining_Entity (N), Aspect_Address);

         --  On type declarations, rewrite the literal aspects to use the
         --  ultimate alias if any.

         elsif Nkind (N) = N_Full_Type_Declaration then
            Rewrite_Aspect (Defining_Entity (N), Aspect_Real_Literal);
            Rewrite_Aspect (Defining_Entity (N), Aspect_Integer_Literal);
            Rewrite_Aspect (Defining_Entity (N), Aspect_String_Literal);
         end if;

         case Nkind (N) is

            when N_Attribute_Reference =>

               --  References to the Old attribute might not have the
               --  type of their prefix. This might lead to discrepencies and
               --  spurious checks. Use the type of the prefix instead.

               if Attribute_Name (N) = Name_Old then
                  Rewrite_Old_Attribute (N);

               --  In some cases, SPARK expansion is performed before the value
               --  of size attributes is known. Reapply it here on analyzed
               --  nodes (other nodes might not have the needed semantic
               --  information).

               elsif Analyzed (N) then
                  declare
                     Aname   : constant Name_Id := Attribute_Name (N);
                     Attr_Id : constant Attribute_Id :=
                       Get_Attribute_Id (Aname);
                  begin
                     if Attr_Id
                        in Attribute_Object_Size
                         | Attribute_Size
                         | Attribute_VADS_Size
                         | Attribute_Value_Size
                     then
                        Expand_Size_Attribute (N);
                     end if;
                  end;
               end if;

            when N_Real_Literal =>
               Rewrite_Real_Literal (N);

            --  Replace renamings and inherited subprograms by the subprogram
            --  they rename or inherit.

            when N_Identifier | N_Expanded_Name | N_Op | N_Operator_Symbol =>
               Rewrite_Subprogram_Reference (N);

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

            when N_Package_Body | N_Subprogram_Body =>
               if Is_Generic_Unit (Unique_Defining_Entity (N)) then
                  return Skip;
               end if;

            --  Ignore freeze entities, because front end might not care to set
            --  all of their fields (such as Scope or Ekind).

            when N_Freeze_Entity =>
               return Skip;

            --  Traverse expressions for DIC procedures

            when N_Full_Type_Declaration =>

               --  Frontend rewrites declarations of derived types, so only
               --  their original node comes from source.

               if Comes_From_Source (Original_Node (N)) then
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

            when N_Subprogram_Declaration =>

               --  We always unconditionally complete the null procedure with a
               --  null body in GNATprove, because some checks in GNATprove are
               --  applied to this body when it is analyzed.

               if Nkind (Specification (N)) = N_Procedure_Specification
                 and then Null_Present (Specification (N))
               then
                  Rewrite_Null_Procedure (N);
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
