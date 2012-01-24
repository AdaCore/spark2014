------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Alfa;                  use Alfa;
with Alfa.Common;           use Alfa.Common;
with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;

with Atree;                 use Atree;
with Einfo;                 use Einfo;
with Namet;         use Namet;
with Nlists;                use Nlists;
with Sinfo;                 use Sinfo;
with Snames;                use Snames;
with Stand;                 use Stand;
with String_Utils;          use String_Utils;
with VC_Kinds;              use VC_Kinds;

with Why;                   use Why;
with Why.Atree.Builders;    use Why.Atree.Builders;
with Why.Atree.Mutators;    use Why.Atree.Mutators;
with Why.Gen.Binders;       use Why.Gen.Binders;
with Why.Gen.Decl;          use Why.Gen.Decl;
with Why.Gen.Expr;          use Why.Gen.Expr;
with Why.Gen.Names;         use Why.Gen.Names;
with Why.Gen.Progs;         use Why.Gen.Progs;
with Why.Gen.Terms;         use Why.Gen.Terms;
with Why.Inter;             use Why.Inter;
with Why.Conversions;       use Why.Conversions;
with Why.Sinfo;             use Why.Sinfo;
with Why.Types;     use Why.Types;

with Gnat2Why.Decls;        use Gnat2Why.Decls;
with Gnat2Why.Expr;         use Gnat2Why.Expr;
with Gnat2Why.Types;        use Gnat2Why.Types;
with Gnat2Why.Driver; use Gnat2Why.Driver;

package body Gnat2Why.Subprograms is

   ---------------------
   -- Local Variables --
   ---------------------

   --  Expressions X'Old and F'Result are normally expanded into references to
   --  saved values of variables by the frontend, but this expansion does not
   --  apply to the original postcondition. It is this postcondition which
   --  is translated by gnat2why into a program to detect possible run-time
   --  errors, therefore a special mechanism is needed to deal with expressions
   --  X'Old and F'Result.

   Result_Name : W_Identifier_Id := Why_Empty;
   --  Name to use for occurrences of F'Result in the postcondition. It should
   --  be equal to Why_Empty when we are not generating code for detecting
   --  run-time errors in the postcondition.

   type Old_Node is record
      Ada_Node : Node_Id;
      Why_Name : Name_Id;
   end record;
   --  Ada_Node is an expression whose 'Old attribute is used in a
   --  postcondition. Why_Name is the name to use for Ada_Node'Old in Why.

   package Old_Nodes is new Ada.Containers.Doubly_Linked_Lists (Old_Node);

   Old_List : Old_Nodes.List;
   --  List of all expressions whose 'Old attribute is used in the current
   --  postcondition, together with the translation of the corresponding
   --  expression in Why.
   --
   --  The list is cleared before generating Why code for a postcondition,
   --  filled during the translation, and used afterwards to generate necessary
   --  the copy instructions.

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array;
   --  Compute arguments corresponding to logical parameters Binders for
   --  subprogram E.

   function Compute_Binders (E : Entity_Id) return Binder_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  a singleton of unit type if E has no parameters.

   function Compute_Context
     (Params : Translation_Params;
      E            : Entity_Id;
      Initial_Body : W_Prog_Id;
      Post_Check   : W_Prog_Id) return W_Prog_Id;
   --  Deal with object declarations at the beginning of the function.
   --  For local variables that originate from the source, simply assign
   --  the new value to the variable; Such variables have been declared
   --  globally.
   --  For local variables that are introduced by the compiler, add a "let"
   --  binding to Why body for each local variable of the procedure.

   function Compute_Effects (E : Entity_Id) return W_Effects_Id;
   --  Compute the effects of the generated Why function.

   function Compute_Logic_Binders (E : Entity_Id) return Binder_Array;
   --  Return Why binders for the parameters and read effects of function E.
   --  The array is a singleton of unit type if E has no parameters and no
   --  effects.

   function Compute_Raw_Binders (E : Entity_Id) return Binder_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  empty if E has no parameters.

   function Compute_Spec
     (Params : Translation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  Compute the precondition or postcondition of the generated Why function.
   --  Kind is Name_Precondition or Name_Postcondition to specify which one is
   --  computed.

   function Get_Location_For_Postcondition (E : Entity_Id) return Node_Id;
   --  Return a node with a proper location for the postcondition of E, if any

   ---------------------
   -- Compute_Binders --
   ---------------------

   function Compute_Binders (E : Entity_Id) return Binder_Array is
      Binders : constant Binder_Array := Compute_Raw_Binders (E);
   begin
      --  If E has no parameters, return a singleton of unit type

      if Binders'Length = 0 then
         return (1 => Unit_Param);
      else
         return Binders;
      end if;
   end Compute_Binders;

   ---------------------------
   -- Compute_Logic_Binders --
   ---------------------------

   function Compute_Logic_Binders (E : Entity_Id) return Binder_Array is
      Binders     : constant Binder_Array := Compute_Raw_Binders (E);
      Read_Names  : Name_Set.Set;
      Num_Binders : Integer;
      Count       : Integer;

   begin
      --  Collect global variables potentially read

      Read_Names := Get_Reads (E);

      --  If E has no parameters and no read effects, return a singleton of
      --  unit type.

      Num_Binders := Binders'Length + Integer (Read_Names.Length);

      if Num_Binders = 0 then
         return (1 => Unit_Param);

      else
         declare
            Result : Binder_Array (1 .. Num_Binders);

         begin
            --  First, copy all binders for parameters of E

            Result (1 .. Binders'Length) := Binders;

            --  Next, add binders for read effects of E

            Count := Binders'Length + 1;
            for R of Read_Names loop
               Result (Count) :=
                 (Ada_Node => Empty,
                  B_Name   => New_Identifier (R.all),
                  B_Type   =>
                    New_Abstract_Type (Name => Object_Type_Name.Id (R.all)),
                  Modifier => None);
               Count := Count + 1;
            end loop;

            return Result;
         end;
      end if;
   end Compute_Logic_Binders;

   -------------------------
   -- Compute_Raw_Binders --
   -------------------------

   function Compute_Raw_Binders (E : Entity_Id) return Binder_Array is
      Params : constant List_Id :=
                 Parameter_Specifications (Get_Subprogram_Spec (E));
      Result : Binder_Array (1 .. Integer (List_Length (Params)));
      Param  : Node_Id;
      Count  : Integer;

   begin
      Param := First (Params);
      Count := 1;
      while Present (Param) loop
         declare
            Id   : constant Node_Id := Defining_Identifier (Param);
            Name : constant W_Identifier_Id := Transform_Ident (Id);
         begin
            Result (Count) :=
              (Ada_Node => Param,
               B_Name   => Name,
               Modifier => (if Is_Mutable (Id) then Ref_Modifier else None),
               B_Type   => +Why_Prog_Type_Of_Ada_Obj (Id, True));
            Next (Param);
            Count := Count + 1;
         end;
      end loop;

      return Result;
   end Compute_Raw_Binders;

   ------------------
   -- Compute_Spec --
   ------------------

   function Compute_Spec
     (Params : Translation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Cur_Spec : W_Expr_Id := New_Literal (Value  => EW_True,
                                           Domain => Domain);
      PPC      : Node_Id;

   begin
      PPC := Spec_PPC_List (Contract (E));
      while Present (PPC) loop
         if Pragma_Name (PPC) = Kind then
            declare
               Expr : constant Node_Id :=
                        Expression
                          (First (Pragma_Argument_Associations (PPC)));
            begin
               Cur_Spec :=
                 New_And_Then_Expr
                   (Left   => Transform_Expr (Expr, Domain, Params),
                    Right  => Cur_Spec,
                    Domain => Domain);
            end;
         end if;

         PPC := Next_Pragma (PPC);
      end loop;

      return Cur_Spec;
   end Compute_Spec;

   --------------------------------------
   -- Generate_VCs_For_Subprogram_Spec --
   --------------------------------------

   procedure Generate_VCs_For_Subprogram_Spec
     (File : W_File_Id;
      E    : Entity_Id)
   is
      Name    : constant String := Full_Name (E);
      Binders : constant Binder_Array := Compute_Binders (E);
      Params  : constant Translation_Params :=
                  (File        => File,
                   Phase       => Generate_VCs_For_Pre,
                   Ref_Allowed => True);
   begin
      Emit
        (File,
         New_Function_Def
           (Domain  => EW_Prog,
            Name    => New_Pre_Check_Name.Id (Name),
            Binders => Binders,
            Def     => Compute_Spec (Params, E, Name_Precondition, EW_Prog)));
   end Generate_VCs_For_Subprogram_Spec;

   ------------------
   -- Name_For_Old --
   ------------------

   function Name_For_Old (N : Node_Id) return W_Identifier_Id is
      Cnt : constant Natural := Natural (Old_List.Length);
      Rec : constant Old_Node :=
              (Ada_Node => N,
               Why_Name => NID ("__gnatprove_old___" & Int_Image (Cnt)));
   begin
      Old_List.Append (Rec);
      return New_Identifier (Symbol => Rec.Why_Name, Domain => EW_Term);
   end Name_For_Old;

   ---------------------
   -- Name_For_Result --
   ---------------------

   function Name_For_Result return W_Identifier_Id is
   begin
      pragma Assert (Result_Name /= Why_Empty);
      return Result_Name;
   end Name_For_Result;

   ---------------------
   -- Compute_Binders --
   ---------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array
   is
      Cnt    : Integer := 1;
      Result : W_Expr_Array (1 .. Binders'Last);
      Ada_Binders : constant List_Id :=
                      Parameter_Specifications (Get_Subprogram_Spec (E));
      Arg_Length  : constant Nat := List_Length (Ada_Binders);

   begin
      if Arg_Length = 0
        and then not Has_Global_Reads (E)
      then
         return W_Expr_Array'(1 => New_Void);
      end if;

      while Cnt <= Integer (Arg_Length) loop
         Result (Cnt) := +Binders (Cnt).B_Name;
         Cnt := Cnt + 1;
      end loop;

      while Cnt <= Binders'Last loop
         Result (Cnt) :=
           New_Deref (Right => Binders (Cnt).B_Name);
         Cnt := Cnt + 1;
      end loop;

      return Result;
   end Compute_Args;

   ---------------------
   -- Compute_Effects --
   ---------------------

   function Compute_Effects (E : Entity_Id) return W_Effects_Id is
      Read_Names      : Name_Set.Set;
      Write_Names     : Name_Set.Set;
      Write_All_Names : UString_Set.Set;
      Eff             : constant W_Effects_Id := New_Effects;

      Ada_Binders : constant List_Id :=
                      Parameter_Specifications (Get_Subprogram_Spec (E));

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

   ------------------------------------
   -- Get_Location_For_Postcondition --
   ------------------------------------

   function Get_Location_For_Postcondition (E : Entity_Id) return Node_Id is
      PPC : Node_Id;

   begin
      PPC := Spec_PPC_List (Contract (E));
      while Present (PPC) loop
         if Pragma_Name (PPC) = Name_Postcondition then
            return Expression (First (Pragma_Argument_Associations (PPC)));
         end if;

         PPC := Next_Pragma (PPC);
      end loop;

      return Empty;
   end Get_Location_For_Postcondition;

   ---------------------
   -- Compute_Context --
   ---------------------

   function Compute_Context
     (Params : Translation_Params;
      E            : Entity_Id;
      Initial_Body : W_Prog_Id;
      Post_Check   : W_Prog_Id) return W_Prog_Id
   is
      R        : W_Prog_Id := Initial_Body;
      Node : constant Node_Id := Get_Subprogram_Body (E);
   begin
      R := Transform_Declarations_Block (Declarations (Node), R);

      --  Enclose the subprogram body in a try-block, so that return
      --  statements can be translated as raising exceptions.

      declare
         Raise_Stmt : constant W_Prog_Id :=
                        New_Raise
                          (Ada_Node => Node,
                           Name     => New_Result_Exc_Identifier.Id);
         Result_Var : constant W_Prog_Id :=
                        (if Ekind (E) = E_Function then
                         New_Deref
                           (Ada_Node => Node,
                            Right    => Result_Name)
                         else New_Void);
      begin
         R :=
           New_Try_Block
             (Prog    => Sequence (R, Raise_Stmt),
              Handler =>
                (1 =>
                   New_Handler
                     (Name => New_Result_Exc_Identifier.Id,
                      Def  => Sequence (Post_Check, Result_Var))));
      end;

      declare
         use Old_Nodes;
         C : Cursor := Old_List.First;
      begin
         while Has_Element (C) loop
            declare
               N : constant Old_Node := Element (C);
            begin
               R :=
                 New_Binding
                   (Name    =>
                        New_Identifier (Symbol => N.Why_Name,
                                        Domain => EW_Prog),
                    Def     => +Transform_Expr (N.Ada_Node, EW_Prog, Params),
                    Context => +R);
               Next (C);
            end;
         end loop;
      end;
      return R;
   end Compute_Context;

   ----------------------------------------
   -- Translate_Expression_Function_Body --
   ----------------------------------------

   procedure Translate_Expression_Function_Body
     (File : W_File_Id;
      E    : Entity_Id)
   is
      Name       : constant String := Full_Name (E);
      Expr_Fun_N : constant Node_Id := Get_Expression_Function (E);
      pragma Assert (Present (Expr_Fun_N));
      Logic_Func_Binders : constant Binder_Array :=
                             Compute_Logic_Binders (E);

      Params : constant Translation_Params :=
                 (File        => File,
                  Phase       => Translation,
                  Ref_Allowed => False);

   begin
      --  Given an expression function F with expression E, define an axiom
      --  that states that: "for all <args> => F(<args>) = E".
      --  There is no need to use the precondition here, as the above axiom
      --  is always sound.

      if Etype (E) = Standard_Boolean then
         Emit
           (File,
            New_Defining_Bool_Axiom
              (Name    => Logic_Func_Name.Id (Name),
               Binders => Logic_Func_Binders,
               Def     => +Transform_Expr (Expression (Expr_Fun_N),
                                           EW_Pred,
                                           Params)));

      else
         Emit
           (File,
            New_Defining_Axiom
              (Name        => Logic_Func_Name.Id (Name),
               Return_Type => Get_EW_Type (Expression (Expr_Fun_N)),
               Binders     => Logic_Func_Binders,
               Def         =>
               +Transform_Expr
                 (Expression (Expr_Fun_N),
                  Expected_Type => EW_Abstract (Etype (E)),
                  Domain        => EW_Term,
                  Params        => Params)));
      end if;
   end Translate_Expression_Function_Body;

   -------------------------------
   -- Translate_Subprogram_Spec --
   -------------------------------

   procedure Translate_Subprogram_Spec
     (File : W_File_Id;
      E    : Entity_Id)
   is
      Name         : constant String := Full_Name (E);
      Effects      : constant W_Effects_Id := Compute_Effects (E);
      Logic_Func_Binders : constant Binder_Array :=
                             Compute_Logic_Binders (E);

      Params : constant Translation_Params :=
                 (File        => File,
                  Phase       => Translation,
                  Ref_Allowed => True);

      Pre          : constant W_Pred_Id :=
              +Compute_Spec (Params, E, Name_Precondition, EW_Pred);
      Post         : constant W_Pred_Id :=
              +Compute_Spec (Params, E, Name_Postcondition, EW_Pred);
      Func_Binders : constant Binder_Array := Compute_Binders (E);

   begin
      if Ekind (E) = E_Function then
         declare
            Logic_Func_Args    : constant W_Expr_Array :=
                                   Compute_Args (E, Logic_Func_Binders);

            --  Each function has in its postcondition that its result is equal
            --  to the application of the corresponding logic function to the
            --  same arguments.

            Param_Post : constant W_Pred_Id :=
                            +New_And_Expr
                              (Left   => New_Relation
                                   (Op      => EW_Eq,
                                    Op_Type =>
                                      Get_EW_Type (+Why_Logic_Type_Of_Ada_Type
                                      (Etype (E))),
                                    Left    => +New_Result_Term,
                                    Right   =>
                                    New_Call
                                      (Domain  => EW_Term,
                                       Name    =>
                                         Logic_Func_Name.Id (Name),
                                       Args    => Logic_Func_Args),
                                    Domain => EW_Pred),
                               Right  => +Post,
                               Domain => EW_Pred);

         begin
            --  Generate a logic function

            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => Logic_Func_Name.Id (Name),
                  Binders     => Logic_Func_Binders,
                  Return_Type =>
                     +Why_Logic_Type_Of_Ada_Type
                       (Etype (E))));

            Emit
              (File,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Program_Func_Name.Id (Name),
                  Binders     => Func_Binders,
                  Return_Type => +Why_Logic_Type_Of_Ada_Type (Etype (E)),
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post));
         end;
      else
         Emit
           (File,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => Program_Func_Name.Id (Name),
               Binders     => Func_Binders,
               Return_Type => New_Base_Type (Base_Type => EW_Unit),
               Effects     => Effects,
               Pre         => Pre,
               Post        => Post));
      end if;
   end Translate_Subprogram_Spec;

   --------------------------------------
   -- Generate_VCs_For_Subprogram_Body --
   --------------------------------------

   procedure Generate_VCs_For_Subprogram_Body
     (File : W_File_Id;
      E    : Entity_Id)
   is
      Name       : constant String := Full_Name (E);
      Body_N     : constant Node_Id := Get_Subprogram_Body (E);
      Post_N     : constant Node_Id := Get_Location_For_Postcondition (E);
      Pre        : W_Pred_Id;
      Post       : W_Pred_Id;
      Post_Check : W_Prog_Id;
      Params     : Translation_Params;

   begin
      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Old_List.Clear;
      Result_Name := New_Result_Temp_Identifier.Id (Name);

      --  Generate code to detect possible run-time errors in the postcondition

      Params := (File        => File,
                 Phase       => Generate_VCs_For_Post,
                 Ref_Allowed => True);
      Post_Check := +Compute_Spec (Params, E, Name_Postcondition, EW_Prog);

      --  Set the phase to Generate_VCs_For_Body from now on, so that
      --  occurrences of F'Result are properly translated as Result_Name.

      Params := (File        => File,
                 Phase       => Generate_VCs_For_Body,
                 Ref_Allowed => True);

      --  Translate contract of E

      Pre  := +Compute_Spec (Params, E, Name_Precondition, EW_Pred);
      Post := +Compute_Spec (Params, E, Name_Postcondition, EW_Pred);

      --  Declare a global variable to hold the result of a function

      if Ekind (E) = E_Function then
         Emit
           (File,
            New_Global_Ref_Declaration
              (Name     => Result_Name,
               Ref_Type => Why_Logic_Type_Of_Ada_Type (Etype (E))));
      end if;

      --  Generate code to detect possible run-time errors in body

      Emit
        (File,
         New_Function_Def
           (Domain  => EW_Prog,
            Name    => New_Definition_Name.Id (Name),
            Binders => (1 => Unit_Param),
            Pre     => Pre,
            Post    =>
              +New_Located_Expr (Post_N, +Post, VC_Postcondition, EW_Pred),
            Def     =>
              +Compute_Context
                (Params,
                 E,
                 Transform_Statements
                   (Statements
                     (Handled_Statement_Sequence (Body_N))),
                 New_Ignore (Prog => Post_Check))));

   end Generate_VCs_For_Subprogram_Body;

end Gnat2Why.Subprograms;
