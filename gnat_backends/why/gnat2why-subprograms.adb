------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Alfa;                  use Alfa;
with Alfa.Common;           use Alfa.Common;
with Alfa.Definition;       use Alfa.Definition;
with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;

with Atree;                 use Atree;
with Debug;
with Einfo;                 use Einfo;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Snames;                use Snames;
with Stand;                 use Stand;
with VC_Kinds;              use VC_Kinds;

with Why;                   use Why;
with Why.Atree.Accessors;   use Why.Atree.Accessors;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Mutators;    use Why.Atree.Mutators;
with Why.Atree.Tables;      use Why.Atree.Tables;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Expr;          use Why.Gen.Expr;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Preds;         use Why.Gen.Preds;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Conversions;       use Why.Conversions;
with Why.Inter;             use Why.Inter;
with Why.Sinfo;             use Why.Sinfo;
with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Expr;         use Gnat2Why.Expr;
with Gnat2Why.Types;        use Gnat2Why.Types;

package body Gnat2Why.Subprograms is

   function Effect_Is_Empty (E : W_Effects_Id) return Boolean;
   --  Test if the effect in argument is empty.

   function Unit_Param return Binder_Type;
   --  return a dummy binder for a single argument of type unit
   --
   function Effect_Is_Empty (E : W_Effects_Id) return Boolean is
   begin
      return
        (Is_Empty (+Get_Reads (E)) and then
         Is_Empty (+Get_Writes (E)));
   end Effect_Is_Empty;

   ----------------
   -- Unit_Param --
   ----------------

   function Unit_Param return Binder_Type is
   begin
      return
        (B_Name   => New_Identifier ("__void_param"),
         B_Type   => New_Base_Type (Base_Type => EW_Unit),
         Modifier => None,
         Ada_Node => Empty);
   end Unit_Param;

   --------------------------------
   -- Why_Decl_Of_Ada_Subprogram --
   --------------------------------

   procedure Why_Decl_Of_Ada_Subprogram
     (File    : W_File_Id;
      Node    : Node_Id;
      As_Spec : Boolean)
   is
      Spec        : constant Node_Id :=
                      (if Nkind (Node) = N_Subprogram_Body and then
                         Present (Corresponding_Spec (Node))
                       then
                         (if Nkind (Parent (Corresponding_Spec (Node))) =
                            N_Defining_Program_Unit_Name
                          then
                            Parent (Parent (Corresponding_Spec (Node)))
                          else
                            Parent (Corresponding_Spec (Node)))
                       else
                         Specification (Node));
      Name_Str    : constant String  :=
                      Get_Name_String (Chars (Defining_Entity (Spec)));
      Ada_Binders : constant List_Id := Parameter_Specifications (Spec);
      Arg_Length  : constant Nat := List_Length (Ada_Binders);

      function Compute_Binders return Binder_Array;
      --  Compute the arguments of the generated Why function;
      --  use argument (x : void) if the Ada procedure / function has no
      --  arguments.

      function Compute_Context (Initial_Body : W_Prog_Id) return W_Prog_Id;
      --  Deal with object declarations at the beginning of the function.
      --  For local variables that originate from the source, simply assign
      --  the new value to the variable; Such variables have been declared
      --  globally.
      --  For local variables that are introduced by the compiler, add a "let"
      --  binding to Why body for each local variable of the procedure.

      function Compute_Effects return W_Effects_Id;
      --  Compute the effects of the generated Why function.

      function Compute_Spec
         (Kind         : Name_Id;
          Located_Node : out Node_Id;
          Domain       : EW_Domain) return W_Expr_Id;
      --  Compute the precondition of the generated Why functions.
      --  Pass the Kind Name_Precondition or Name_Postcondition to decide if
      --  you want the pre- or postcondition.
      --  Also output a suitable location node, if available.

      function Is_Syntactic_Expr_Function return Node_Id;
      --  Compute if Node is an expression function in the source, also works
      --  for the declaration of an expression function.
      --  If Is_Syntactic_Expr_Function'Result is equal to Node, Node is not
      --  an expression function; otherwise, Is_Syntactic_Expr_Function'Result
      --  is the original node of the expression function.

      ---------------------
      -- Compute_Binders --
      ---------------------

      function Compute_Binders return Binder_Array
      is
         Cur_Binder : Node_Id := First (Ada_Binders);
         Cnt        : Integer := 1;
      begin
         if Arg_Length = 0 then
            return (1 => Unit_Param);
         else
            declare
               Result : Binder_Array :=
                          (1 .. Integer (Arg_Length) => <>);
            begin
               while Present (Cur_Binder) loop
                  declare
                     Id   : constant Node_Id :=
                              Defining_Identifier (Cur_Binder);
                     Name : constant W_Identifier_Id :=
                              Transform_Ident (Id);
                  begin
                     Result (Cnt) :=
                       (Ada_Node => Cur_Binder,
                        B_Name   => Name,
                        Modifier =>
                          (if Is_Mutable (Id) then Ref_Modifier else None),
                        B_Type => +Why_Prog_Type_Of_Ada_Obj (Id, True));
                     Next (Cur_Binder);
                     Cnt := Cnt + 1;
                  end;
               end loop;
               return Result;
            end;
         end if;
      end Compute_Binders;

      ---------------------
      -- Compute_Context --
      ---------------------

      function Compute_Context (Initial_Body : W_Prog_Id) return W_Prog_Id
      is
         Cur_Decl : Node_Id := Last (Declarations (Node));
         R        : W_Prog_Id := Initial_Body;
      begin
         while Nkind (Cur_Decl) /= N_Empty loop
            case Nkind (Cur_Decl) is
               when N_Object_Declaration =>
                  R := Sequence (Assignment_of_Obj_Decl (Cur_Decl), R);

               when others =>
                  null;

            end case;
            Cur_Decl := Prev (Cur_Decl);
         end loop;

         --  Enclose the subprogram body in a try-block, so that return
         --  statements can be translated as raising exceptions.

         declare
            Raise_Stmt : constant W_Prog_Id :=
                           New_Raise
                             (Ada_Node => Node,
                              Name     => New_Result_Exc_Identifier.Id);
            Result_Var : constant W_Prog_Id :=
                           (if Nkind (Spec) = N_Function_Specification then
                              New_Unary_Op
                                (Ada_Node => Node,
                                 Op       => EW_Deref,
                                 Right    => +New_Result_Temp_Identifier.Id,
                                 Op_Type  => EW_Int)
                            else New_Void);
         begin
            R :=
              New_Try_Block
                (Prog    => Sequence (R, Raise_Stmt),
                 Handler =>
                   (1 =>
                      New_Handler
                        (Name => New_Result_Exc_Identifier.Id,
                         Def  => Result_Var)));
         end;

         --  Declare a local variable to hold the result of a function

         if Nkind (Spec) = N_Function_Specification then
            declare
               Rvalue : constant W_Prog_Id :=
                          New_Simpl_Any_Expr
                            (New_Base_Type
                               (Base_Type => EW_Abstract,
                                Ada_Node  =>
                                  Type_Of_Node
                                    (Defining_Entity (Spec))));
            begin
               R :=
                 New_Binding_Ref
                   (Ada_Node => Cur_Decl,
                    Name     => New_Result_Temp_Identifier.Id,
                    Def      => Rvalue,
                    Context  => R);
            end;
         end if;

         return R;
      end Compute_Context;

      ---------------------
      -- Compute_Effects --
      ---------------------

      function Compute_Effects return W_Effects_Id is
         E               : constant Entity_Id := Unique_Defining_Entity (Node);
         Read_Names      : Name_Set.Set;
         Write_Names     : Name_Set.Set;
         Write_All_Names : UString_Set.Set;
         Eff             : constant W_Effects_Id := New_Effects;

      begin
         --  Collect global variables potentially read and written

         Read_Names  := Get_Reads (E);
         Write_Names := Get_Writes (E);

         --  Workaround for K526-008 and K525-019

         --  for Name of Write_Names loop
         --     Write_All_Names.Include (To_Unbounded_String (Name.all));
         --  end loop;

         declare
            use Name_Set;

            C : Cursor := Write_Names.First;
         begin
            while C /= No_Element loop
               Write_All_Names.Include (To_Unbounded_String (Element (C).all));
               Next (C);
            end loop;
         end;

         --  Add all OUT and IN OUT parameters as potential writes

         declare
            Arg : Node_Id;
            Id  : Entity_Id;
         begin
            if Is_Non_Empty_List (Ada_Binders) then
               Arg := First (Ada_Binders);
               while Present (Arg) loop
                  Id := Defining_Identifier (Arg);

                  if Ekind_In (Id, E_Out_Parameter, E_In_Out_Parameter) then
                     Write_All_Names.Include
                       (To_Unbounded_String (Full_Name (Id)));
                  end if;

                  Next (Arg);
               end loop;
            end if;
         end;

         --  Workaround for K526-008 and K525-019

         --  for Name of Read_Names loop
         --     Effects_Append_To_Reads (Eff, New_Identifier (Name.all));
         --  end loop;

         declare
            use Name_Set;

            C : Cursor := Read_Names.First;
         begin
            while C /= No_Element loop
               Effects_Append_To_Reads (Eff, New_Identifier (Element (C).all));
               Next (C);
            end loop;
         end;

         --  Workaround for K526-008 and K525-019

         --  for Name of Write_All_Names loop
         --     Effects_Append_To_Writes (Eff,
         --                               New_Identifier (To_String (Name)));
         --  end loop;

         declare
            use UString_Set;

            C : Cursor := Write_All_Names.First;
         begin
            while C /= No_Element loop
               Effects_Append_To_Writes (Eff,
                                         New_Identifier
                                           (To_String (Element (C))));
               Next (C);
            end loop;
         end;

         return +Eff;
      end Compute_Effects;

      ------------------
      -- Compute_Spec --
      ------------------

      function Compute_Spec
         (Kind         : Name_Id;
          Located_Node : out Node_Id;
          Domain       : EW_Domain) return W_Expr_Id
      is
         Corr_Spec      : Node_Id;
         Cur_Spec       : W_Expr_Id := New_Literal (Value  => EW_True,
                                                    Domain => Domain);
         Found_Location : Boolean := False;
         PPCs           : Node_Id;

      begin
         if Nkind (Node) = N_Subprogram_Declaration then
            Corr_Spec := Defining_Entity (Spec);
         else
            Corr_Spec := Corresponding_Spec (Node);
         end if;

         if Nkind (Corr_Spec) = N_Empty then
            return Cur_Spec;
         end if;

         PPCs := Spec_PPC_List (Contract (Corr_Spec));
         while Present (PPCs) loop
            if Pragma_Name (PPCs) = Kind then
               declare
                  Ada_Spec : constant Node_Id :=
                               Expression
                                 (First (Pragma_Argument_Associations (PPCs)));
               begin
                  if not Found_Location then
                     Located_Node := Ada_Spec;
                     Found_Location := True;
                  end if;

                  Cur_Spec :=
                     New_And_Then_Expr
                       (Left   => Transform_Expr (Ada_Spec, Domain),
                        Right  => Cur_Spec,
                        Domain => Domain);
               end;
            end if;

            PPCs := Next_Pragma (PPCs);
         end loop;

         return Cur_Spec;
      end Compute_Spec;

      --------------------------------
      -- Is_Syntactic_Expr_Function --
      --------------------------------

      function Is_Syntactic_Expr_Function return Node_Id
      is
         Tmp_Node : Node_Id := Original_Node (Parent (Spec));
      begin
         --  Usually, it is sufficient to check for the original node of the
         --  function (but for some reason we have to descend to the spec and
         --  move up to another parent).

         if Nkind (Tmp_Node) = N_Expression_Function then
            return Tmp_Node;
         end if;

         --  But if we are at the function declaration, it is possible that
         --  the function definition is given later, using an expression
         --  function. We check this second possibility here.

         if Nkind (Node) = N_Subprogram_Declaration then
            Tmp_Node :=
              Original_Node (Parent (Parent (Corresponding_Body (Node))));

            if Nkind (Tmp_Node) = N_Expression_Function then
               return Tmp_Node;
            end if;

         --  ??? I don't know in which situation we need this case ...

         else
            Tmp_Node :=
               Original_Node (Parent (Parent (Corresponding_Spec (Node))));

            if Nkind (Tmp_Node) = N_Expression_Function then
               return Tmp_Node;
            end if;
         end if;

         return Node;
      end Is_Syntactic_Expr_Function;

      Func_Binders : constant Binder_Array := Compute_Binders;
      Dummy_Node   : Node_Id;
      Pre          : constant W_Pred_Id :=
                       +Compute_Spec (Name_Precondition, Dummy_Node, EW_Pred);
      Loc_Node     : Node_Id := Empty;
      Post         : constant W_Pred_Id :=
                       +Compute_Spec (Name_Postcondition, Loc_Node, EW_Pred);
      Orig_Node    : constant Node_Id := Is_Syntactic_Expr_Function;
      Effects      : constant W_Effects_Id := Compute_Effects;
      Is_Expr_Func : constant Boolean :=
                       Nkind (Spec) = N_Function_Specification
                         and then
                       Effect_Is_Empty (Effects)
                         and then
                       Expression_Functions_All_The_Way
                         (Defining_Entity (Spec))
                         and then
                       Orig_Node /= Node
                         and then
                       Get_Kind (+Post) = W_Literal
                         and then
                       Get_Value (+Post) = EW_True;

   --  Start of processing for Why_Decl_Of_Ada_Subprogram

   begin
      if Nkind (Node) = N_Subprogram_Body
        and then not As_Spec
      then
         Emit
           (File,
            New_Function_Def
              (Domain  => EW_Prog,
               Name    => New_Pre_Check_Name.Id (Name_Str),
               Binders => Func_Binders,
               Def     => +Compute_Spec (Name_Precondition,
                                         Dummy_Node,
                                         EW_Prog)));

         if Is_Expr_Func then
            if Etype (Defining_Entity (Spec)) = Standard_Boolean then
               Emit
                 (File,
                  New_Defining_Bool_Axiom
                    (Name    => Logic_Func_Name.Id (Name_Str),
                     Binders => Func_Binders,
                     Pre     => Pre,
                     Def     => +Transform_Expr (Expression (Orig_Node),
                                                       EW_Pred)));

            else
               Emit
                 (File,
                  New_Defining_Axiom
                    (Name        => Logic_Func_Name.Id (Name_Str),
                     Return_Type => Get_EW_Type (Expression (Orig_Node)),
                     Binders     => Func_Binders,
                     Pre         => Pre,
                     Def         =>
                       +Transform_Expr
                         (Expression (Orig_Node), EW_Term)));
            end if;
         end if;

         if Is_Expr_Func or else not Debug.Debug_Flag_Dot_GG then
            Emit
              (File,
               New_Function_Def
                 (Domain  => EW_Prog,
                  Name    => New_Definition_Name.Id (Name_Str),
                  Binders => (1 => Unit_Param),
                  Pre     => Pre,
                  Post    =>
                    +New_Located_Expr
                      (Loc_Node,
                       +Post,
                       VC_Postcondition,
                       EW_Pred),
                  Def     =>
                    +Compute_Context
                      (Transform_Statements
                        (Statements
                          (Handled_Statement_Sequence (Node))))));
         end if;

      else
         declare
            Ret_Type   : constant W_Primitive_Type_Id :=
                           (if Nkind (Spec) = N_Function_Specification then
                              +Why_Logic_Type_Of_Ada_Type
                                (Entity (Result_Definition (Spec)))
                            else
                              New_Base_Type (Base_Type => EW_Unit));
            Param_Post : constant W_Pred_Id :=
                           (if Is_Expr_Func then
                              (if Entity (Result_Definition (Spec)) =
                                              Standard_Boolean
                               then
                                 New_Equal_Bool
                                   (Left  => New_Result_Term,
                                    Right =>
                                      +Transform_Expr
                                        (Expression (Orig_Node), EW_Pred))
                               else
                                 New_Relation
                                   (Op      => EW_Eq,
                                    Op_Type =>
                                      Get_EW_Type (Expression (Orig_Node)),
                                    Left    => +New_Result_Term,
                                    Right   =>
                                      +Transform_Expr
                                        (Expression (Orig_Node), EW_Term)))
                            else Post);
         begin
            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Program_Func_Name.Id (Name_Str),
                  Binders     => Func_Binders,
                  Return_Type => Ret_Type,
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post));

            if Is_Expr_Func then
               Emit
                 (File,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => Logic_Func_Name.Id (Name_Str),
                     Binders     => Func_Binders,
                     Return_Type =>
                       +Why_Logic_Type_Of_Ada_Type
                         (Etype (Defining_Entity (Spec)))));
            end if;
         end;
      end if;
   end Why_Decl_Of_Ada_Subprogram;

end Gnat2Why.Subprograms;
