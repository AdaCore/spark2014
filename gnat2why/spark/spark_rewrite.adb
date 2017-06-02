------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S P A R K _ R E W R I T E                        --
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
with Einfo;                  use Einfo;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Aux;                use Sem_Aux;
with Sem_Eval;               use Sem_Eval;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Snames;                 use Snames;
with SPARK_Util.Subprograms;
with Tbuild;                 use Tbuild;

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

   procedure Rewrite_Subprogram_Instantiation (N : Node_Id)
   with Pre => Nkind (N) in N_Subprogram_Instantiation;
   --  Replace names in instances of generic subprograms with names of
   --  the original subprograms; we prefer the original names when outputting
   --  error messages and generating Why code.

   procedure Rewrite_Real_Literal (N : Node_Id);
   --  Rewrite real literals that are not sub-expressions of static expressions
   --  into machine numbers, when the frontend has not done so already as part
   --  of Eval_Real_Literal. This can only be performed here and not as part
   --  of evaluation or expansion in the frontend, because the information that
   --  the parent expression is static is only available after the real literal
   --  node has been evaluated and expanded.

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
            Const_Expr  : constant Node_Id := Constant_Value (Entity (N));
            Range_Check : constant Boolean := Do_Range_Check (N);
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
               Set_Do_Range_Check (N, Range_Check);
            end if;
         end;
      end if;
   end Rewrite_Identifier;

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
      PK  : constant Node_Kind := Nkind (Par);
   begin
      if PK in N_Subexpr
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

      Orig_Name_Id : constant Name_Id := Chars (Defining_Unit_Name (N));
      --  ??? how about homonyms?

      Wrapper_Package : constant Entity_Id :=
        Defining_Entity (Instance_Spec (N));

      pragma Assert (Ekind (Wrapper_Package) = E_Package);

      function Wrapped_Instance return Entity_Id
      with Post => Ekind (Wrapped_Instance'Result) in E_Function | E_Procedure;
      --  Returns entity of the wrapped instance

      ----------------------
      -- Wrapped_Instance --
      ----------------------

      function Wrapped_Instance return Entity_Id is
         E : Entity_Id;

      begin
         --  The first/next entity chain of a generic subprogram instance
         --  contains all generic formal parameters, followed by the
         --  subprogram declaration. Go directly to that declaration by
         --  skipping the formal part.
         E := First_Entity (Wrapper_Package);

         loop
            pragma Loop_Invariant (Present (E));

            if Is_Subprogram (E)
              and then not Is_Generic_Actual_Subprogram (E)
            then
               return E;
            end if;

            Next_Entity (E);
         end loop;
      end Wrapped_Instance;

   --  Start of processing for Rewrite_Subprogram_Instantiation

   begin
      Set_Chars (Wrapped_Instance, Orig_Name_Id);
   end Rewrite_Subprogram_Instantiation;

   ------------------------------
   -- Rewrite_Compilation_Unit --
   ------------------------------

   procedure Rewrite_Compilation_Unit (N : Node_Id) is

      function Rewrite_Node (N : Node_Id) return Traverse_Result;
      --  Apply expansion operations on a node

      procedure Rewrite_Nodes is
        new Traverse_Proc (Rewrite_Node);

      procedure Rewrite_Unchecked_Type_Conversion (N : Node_Id);
      --  Remove compiler-generated unchecked type conversions, which should
      --  be transparent with our translation, when Do_Range_Check flag is
      --  set on the node. Replace these nodes with the converted expression
      --  where Do_Range_Check is set. This ensures that when translating
      --  the expression, we can effectively ignore the compiler-generated
      --  unchecked type conversion.

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
           and then Nkind (Original_Node (N)) in N_Subprogram_Call | N_Pragma
         then
            Rewrite_Nodes (Original_Node (N));
         end if;

         case Nkind (N) is
            when N_Real_Literal =>
               Rewrite_Real_Literal (N);

            when N_Identifier
               | N_Expanded_Name
            =>
               Rewrite_Identifier (N);

            --  Replace calls to Unchecked_Conversion instances by nodes
            --  N_Unchecked_Type_Conversion, which are marked as coming
            --  from source.

            when N_Subprogram_Call =>
               Rewrite_Call (N);

            --  Replace compiler-generated unchecked type conversions by the
            --  converted expression when required so that the translation of
            --  expressions into Why3 can rely on correct flag placement as
            --  specified in sinfo.ads. We do that here in order to set the
            --  appropriate range check flag on the rewritten expression.

            when N_Unchecked_Type_Conversion =>
               Rewrite_Unchecked_Type_Conversion (N);

            when N_Subprogram_Instantiation =>
               Rewrite_Subprogram_Instantiation (N);

            --  Recursively call the tree rewriting procedure on subunits

            when N_Body_Stub =>
               Rewrite_Nodes (Unit (Library_Unit (N)));

            --  Ignore freeze entities, because front end might not care to set
            --  all of their fields (such as Scope or Ekind).

            when N_Freeze_Entity =>
               return Skip;

            --  Traverse procedure calls rewritten as null statements

            when N_Null_Statement =>
               if Nkind (Original_Node (N)) = N_Procedure_Call_Statement
               then
                  Rewrite_Nodes (Original_Node (N));
               end if;

            --  Traverse expressions for DIC procedures

            when N_Full_Type_Declaration =>
               declare
                  Ty       : constant Entity_Id := Defining_Entity (N);
                  DIC_Subp : Entity_Id;
                  DIC_Expr : Node_Id;

               begin
                  if Has_DIC (Ty) then
                     DIC_Subp := DIC_Procedure (Ty);

                     if Present (DIC_Subp) then
                        DIC_Expr := SPARK_Util.Subprograms.
                          Get_Expr_From_Check_Only_Proc (DIC_Subp);
                        Rewrite_Nodes (DIC_Expr);
                        --  ??? this is slighly different from SPARK_Register;
                        --  both should be unified.
                     end if;
                  end if;
               end;

            when others =>
               null;
         end case;

         return OK;
      end Rewrite_Node;

      ---------------------------------------
      -- Rewrite_Unchecked_Type_Conversion --
      ---------------------------------------

      procedure Rewrite_Unchecked_Type_Conversion (N : Node_Id) is
         Expr : constant Node_Id := Expression (N);
         Typ  : constant Entity_Id := Etype (N);

      begin
         if not Comes_From_Source (N)
           and then Do_Range_Check (N)
         then
            declare
               Ignore : constant Traverse_Result := Rewrite_Node (Expr);
            begin
               Rewrite (Old_Node => N,
                        New_Node => Expr);
               Set_Do_Range_Check (N, True);
               Set_Etype (N, Typ);
            end;
         end if;
      end Rewrite_Unchecked_Type_Conversion;

   --   Start of processing for Rewrite_Compilation_Unit

   begin
      --  Avoid rewriting generic units which are only preanalyzed, which may
      --  cause rewriting to fail, as this is not needed.

      if Is_Generic_Unit (Unique_Defining_Entity (N)) then
         null;

      --  Rewrite_Compilation_Unit is called on the declaration or body of a
      --  library unit (see spec of Sem.Walk_Library_Items), but we need here
      --  to call Rewrite_Nodes on the parent compilation unit node when there
      --  is one, so that aspects rewritten as pragmas after the library unit
      --  declaration or body (listed in Pragmas_After) are also rewritten.

      elsif Present (Parent (N)) then
         Rewrite_Nodes (Parent (N));
      else
         Rewrite_Nodes (N);
      end if;
   end Rewrite_Compilation_Unit;

end SPARK_Rewrite;
