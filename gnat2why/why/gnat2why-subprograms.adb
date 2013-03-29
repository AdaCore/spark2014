------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - S U B P R O G R A M S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with GNAT.Source_Info;

with Atree;                  use Atree;
with Einfo;                  use Einfo;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with Stand;                  use Stand;
with Uintp;                  use Uintp;
with VC_Kinds;               use VC_Kinds;

with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with Why;                    use Why;
with Why.Atree.Accessors;    use Why.Atree.Accessors;
with Why.Atree.Builders;     use Why.Atree.Builders;
with Why.Atree.Mutators;     use Why.Atree.Mutators;
with Why.Conversions;        use Why.Conversions;
--   with Why.Gen.Binders;   use Why.Gen.Binders;
with Why.Gen.Decl;           use Why.Gen.Decl;
with Why.Gen.Expr;           use Why.Gen.Expr;
with Why.Gen.Names;          use Why.Gen.Names;
with Why.Gen.Preds;          use Why.Gen.Preds;
with Why.Gen.Progs;          use Why.Gen.Progs;
with Why.Ids;                use Why.Ids;
with Why.Sinfo;              use Why.Sinfo;
with Why.Types;              use Why.Types;

with Gnat2Why.Decls;         use Gnat2Why.Decls;
with Gnat2Why.Expr;          use Gnat2Why.Expr;
with Gnat2Why.Nodes;         use Gnat2Why.Nodes;
with Gnat2Why.Types;         use Gnat2Why.Types;
with Gnat2Why.Util;          use Gnat2Why.Util;

package body Gnat2Why.Subprograms is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Args
     (E       : Entity_Id;
      Binders : Binder_Array) return W_Expr_Array;
   --  Given a function entity, and an array of logical binders,
   --  compute a call of the logical Why function corresponding to E.
   --  In general, the binder array has *more* arguments than the Ada entity,
   --  because of effects. Note that these effect variables are not bound here,
   --  they refer to the global variables

   function Compute_Context
     (Params       : Transformation_Params;
      E            : Entity_Id;
      Initial_Body : W_Prog_Id;
      Post_Check   : W_Prog_Id;
      Guard_Map    : Ada_To_Why_Ident.Map) return W_Prog_Id;
   --  Deal with object declarations at the beginning of the function.
   --  For local variables that originate from the source, simply assign
   --  the new value to the variable; Such variables have been declared
   --  globally.
   --  For local variables that are introduced by the compiler, add a "let"
   --  binding to Why body for each local variable of the procedure.

   function Compute_Contract_Cases_Entry_Checks
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Prog_Id;
   --  Returns the Why program for checking that the guards of the
   --  Contract_Cases pragma attached to subprogram E (if any) do not raise
   --  run-time errors, that they are disjoint, and that they cover all cases
   --  prescribed by the precondition.

   procedure Compute_Contract_Cases_Exit_Checks
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Guard_Map : out Ada_To_Why_Ident.Map;
      Result    : out W_Prog_Id);
   --  Returns in Result the Why program for checking that the consequence of
   --  enabled guard of the Contract_Cases pragma attached to subprogram E (if
   --  any) does not raise a run-time error, and that it holds. Guard_Map
   --  stores a mapping from guard AST nodes to temporary Why names, so that
   --  the caller can compute the Why expression for these in the pre-state,
   --  and bind them appropriately.

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id;
   --  Returns the postcondition corresponding to the Contract_Cases pragma for
   --  subprogram E (if any), to be used in the postcondition of the program
   --  function.

   function Compute_Effects (File : in out Why_File;
                             E    : Entity_Id) return W_Effects_Id;
   --  Compute the effects of the generated Why function.

   function Compute_Logic_Binders (E : Entity_Id) return Binder_Array;
   --  Return Why binders for the parameters and read effects of function E.
   --  The array is a singleton of unit type if E has no parameters and no
   --  effects.

   function Compute_Raw_Binders (E : Entity_Id) return Binder_Array;
   --  Return Why binders for the parameters of subprogram E. The array is
   --  empty if E has no parameters.

   function Compute_Spec
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
      Domain : EW_Domain) return W_Expr_Id;
   --  Compute the precondition or postcondition of the generated Why function.
   --  Kind is Name_Precondition or Name_Postcondition to specify which one is
   --  computed.

   function Get_Location_For_Postcondition (E : Entity_Id) return Node_Id;
   --  Return a node with a proper location for the postcondition of E, if any

   ------------------------------------------
   -- Complete_Subprogram_Spec_Translation --
   ------------------------------------------

   procedure Complete_Subprogram_Spec_Translation
     (File    : in out Why_File;
      E       : Entity_Id;
      In_Body : Boolean)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
        Base_Name & To_String (WNE_Expr_Fun_Closure);

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module including all necessary axioms for the "
                       & "subprogram "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " declared at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  No filtering is necessary here, as the theory should on the contrary
      --  use the previously defined theory for the subprogram declaration.
      --  Attach the newly created theory as a completion of the existing one.

      Close_Theory (File,
                    Filter_Entity  => Empty,
                    Defined_Entity => E,
                    Do_Closure     => True);

      if In_Body then
         Add_Completion (Base_Name, Name, WF_Context_In_Body);
      else
         Add_Completion (Base_Name, Name, WF_Context_In_Spec);
      end if;
   end Complete_Subprogram_Spec_Translation;

   ------------------
   -- Compute_Args --
   ------------------

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
           New_Deref
             (Right =>
                  To_Why_Id (Get_Name_String
                     (Get_Symbol (Binders (Cnt).B_Name))));
         Cnt := Cnt + 1;
      end loop;

      return Result;
   end Compute_Args;

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

   ---------------------
   -- Compute_Context --
   ---------------------

   function Compute_Context
     (Params       : Transformation_Params;
      E            : Entity_Id;
      Initial_Body : W_Prog_Id;
      Post_Check   : W_Prog_Id;
      Guard_Map    : Ada_To_Why_Ident.Map) return W_Prog_Id
   is
      R    : W_Prog_Id        := Initial_Body;
      Node : constant Node_Id := SPARK_Util.Get_Subprogram_Body (E);
   begin
      R := Transform_Declarations_Block (Declarations (Node), R);

      --  Enclose the subprogram body in a try-block, so that return
      --  statements can be translated as raising exceptions.

      declare
         Raise_Stmt : constant W_Prog_Id :=
                        New_Raise
                          (Ada_Node => Node,
                           Name     => To_Ident (WNE_Result_Exc));
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
                     (Name => To_Ident (WNE_Result_Exc),
                      Def  => Sequence (Post_Check, Result_Var))));
      end;

      R := Bind_From_Mapping_In_Expr (Params, Map_For_Old, R);

      --  Bind value of guard expressions. We do not generate checks for
      --  run-time errors here, as they are already generated in
      --  Compute_Contract_Cases_Entry_Checks.

      R := Bind_From_Mapping_In_Expr (Params => Params,
                                      Map    => Guard_Map,
                                      Expr   => R,
                                      Do_Runtime_Error_Check => False);

      return R;
   end Compute_Context;

   ---------------------
   -- Compute_Effects --
   ---------------------

   function Compute_Effects (File : in out Why_File;
                             E    : Entity_Id) return W_Effects_Id is
      Read_Names      : Name_Set.Set;
      Write_Names     : Name_Set.Set;
      Eff             : constant W_Effects_Id := New_Effects;

      Ada_Binders : constant List_Id :=
                      Parameter_Specifications (Get_Subprogram_Spec (E));

   begin
      --  Collect global variables potentially read and written

      Read_Names  := Get_Reads (E);
      Write_Names := Get_Writes (E);

      for Name of Write_Names loop
         Effects_Append_To_Writes
           (Eff,
            To_Why_Id (Obj => Name.all));
      end loop;

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
                  Effects_Append_To_Writes
                    (Eff,
                     New_Identifier (Name => Full_Name (Id)));
               end if;

               Next (Arg);
            end loop;
         end if;
      end;

      for Name of Read_Names loop
         Effects_Append_To_Reads (Eff, To_Why_Id (Obj => Name.all));
      end loop;

      Add_Effect_Imports (File, Read_Names);
      Add_Effect_Imports (File, Write_Names);

      return +Eff;
   end Compute_Effects;

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
                  B_Name   => New_Identifier (Name => R.all),
                  B_Type   =>
                    New_Abstract_Type (Name => To_Why_Type (R.all)),
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

         --  We do not want to add a dependency to the Id entity here, so we
         --  set the ada node to empty. However, we still need the entity for
         --  the Name_Map of the translation, so we store it in the binder.

         declare
            Id   : constant Node_Id := Defining_Identifier (Param);
            Name : constant W_Identifier_Id :=
              New_Identifier (Ada_Node => Empty, Name => Full_Name (Id));
         begin
            Result (Count) :=
              (Ada_Node => Id,
               B_Name   => Name,
               Modifier =>
                 (if Is_Mutable_In_Why (Id) then Ref_Modifier else None),
               B_Type   => +Why_Prog_Type_Of_Ada_Obj (Id, True));
            Next (Param);
            Count := Count + 1;
         end;
      end loop;

      return Result;
   end Compute_Raw_Binders;

   -----------------------------------------
   -- Compute_Contract_Cases_Entry_Checks --
   -----------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of checks on subprogram entry. In a context
   --  where the precondition is known to hold, it is checked that no
   --  evaluation of a guard can lead to a run-time error, that no more than
   --  one guard evaluates to True (only if there are at least two non-OTHER
   --  guards), and that at least one guard evaluates to True (only in the case
   --  there is no OTHERS).

   --    let guard1 = ... in
   --    let guard2 = ... in
   --    ...
   --    let guardN = ... in

   --  Check that contract cases are disjoint only if there are at least two
   --  non-OTHER guards:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) <= 1)

   --  Check that contract cases are complete only if there is no OTHERS:

   --    assert ((if guard1 = True then 1 else 0) +
   --            (if guard2 = True then 1 else 0) +
   --            ...
   --            (if guardN = True then 1 else 0) >= 1)

   function Compute_Contract_Cases_Entry_Checks
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Prog_Id
   is
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      Guard_Map   : Ada_To_Why_Ident.Map;
      --  Stores a mapping from guard AST nodes to temporary Why names

      Has_Others  : Boolean := False;
      --  Set to True if there is an OTHERS guard

      Count       : W_Expr_Id := New_Integer_Constant (Value => Uint_0);
      --  Count of the guards enabled

      Result      : W_Prog_Id := New_Void;
      --  Why program for these checks

   --  Start of Compute_Contract_Cases_Entry_Checks

   begin
      --  If no Contract_Cases on this subprogram, return the void program

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));

         --  The "others" choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Has_Others := True;

         --  Regular contract case

         else
            declare
               Guard_Ident : constant W_Identifier_Id := New_Temp_Identifier;
               --  Temporary Why name for the current guard

               --  Whether the current guard is enabled
               Enabled     : constant W_Expr_Id :=
                 New_Conditional
                   (Ada_Node    => Case_Guard,
                    Domain      => EW_Term,
                    Condition   =>
                      New_Relation (Domain   => EW_Term,
                                    Op_Type  => EW_Bool,
                                    Left     => +Guard_Ident,
                                    Op       => EW_Eq,
                                    Right    =>
                                      New_Literal (Domain => EW_Term,
                                                   Value  => EW_True)),
                    Then_Part   => New_Integer_Constant (Value => Uint_1),
                    Else_Part   => New_Integer_Constant (Value => Uint_0));
            begin
               Guard_Map.Include (Case_Guard, Guard_Ident);
               Count := New_Binary_Op (Ada_Node => Case_Guard,
                                       Op       => EW_Add,
                                       Op_Type  => EW_Int,
                                       Left     => Count,
                                       Right    => Enabled);
            end;
         end if;

         Next (Contract_Case);
      end loop;

      --  A check that contract cases are disjoint is generated only when there
      --  are at least two guards, and none is an OTHER guard.

      if List_Length (Component_Associations (Aggr)) >= 2
        and then (if List_Length (Component_Associations (Aggr)) = 2
                  then not Has_Others)
      then
         Result := Sequence
           (Result,
            New_Assert
              (Pred => +New_VC_Expr (Prag,
               New_Relation (Domain   => EW_Pred,
                             Op_Type  => EW_Int,
                             Left     => +Count,
                             Op       => EW_Le,
                             Right    =>
                               New_Integer_Constant (Value => Uint_1)),
               VC_Disjoint_Contract_Cases,
               EW_Pred)));
      end if;

      --  A check that contract cases are complete is generated only when there
      --  is no OTHER guard.

      if not Has_Others then
         Result := Sequence
           (Result,
            New_Assert
              (Pred => +New_VC_Expr (Prag,
               New_Relation (Domain   => EW_Pred,
                             Op_Type  => EW_Int,
                             Left     => +Count,
                             Op       => EW_Ge,
                             Right    =>
                               New_Integer_Constant (Value => Uint_1)),
               VC_Complete_Contract_Cases,
               EW_Pred)));
      end if;

      --  Bind value of guard expressions

      Result := Bind_From_Mapping_In_Expr (Params => Params,
                                           Map    => Guard_Map,
                                           Expr   => Result);

      return Result;
   end Compute_Contract_Cases_Entry_Checks;

   ----------------------------------------
   -- Compute_Contract_Cases_Exit_Checks --
   ----------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of checks on subprogram exit. It is checked that
   --  the consequence for the guard that was True on entry also evaluates to
   --  True, without run-time errors.

   --  The following do not include run-time checks:
   --    let guard1 = ... in
   --    let guard2 = ... in
   --    ...
   --    let guardN = ... in

   --  The following do include run-time checks:
   --    assert (if guard1 then consequence1);
   --    assert (if guard2 then consequence2);
   --    ...
   --    assert (if guardN then consequenceN);
   --    assert (if not (guard1 or guard2 ... or guardN) then consequenceN+1);

   procedure Compute_Contract_Cases_Exit_Checks
     (Params    : Transformation_Params;
      E         : Entity_Id;
      Guard_Map : out Ada_To_Why_Ident.Map;
      Result    : out W_Prog_Id)
   is
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;

      Others_Contract_Case : Node_Id := Empty;
      --  Contract case for the OTHERS case, if any

      Others_Guard  : W_Expr_Id := New_Literal (Domain => EW_Term,
                                                Value  => EW_False);
      --  Guard for the OTHERS case, if any

      function Do_One_Contract_Case
        (Contract_Case : Node_Id;
         Enabled       : W_Expr_Id) return W_Prog_Id;
      --  Returns the Why program checking absence of run-time errors and
      --  function verification of the given Contract_Case.

      function Do_One_Contract_Case
        (Contract_Case : Node_Id;
         Enabled       : W_Expr_Id) return W_Prog_Id
      is
         Consequence : constant Node_Id := Expression (Contract_Case);
      begin
         return Sequence
           (New_Ignore
              (Prog =>
                 +W_Expr_Id'(New_Conditional
                   (Ada_Node    => Contract_Case,
                    Domain      => EW_Prog,
                    Condition   => Enabled,
                    Then_Part   =>
                      +Transform_Expr (Consequence, EW_Prog, Params),
                    Else_Part   =>
                      New_Literal (Domain => EW_Prog,
                                   Value  => EW_True)))),
            New_Assert
              (Pred => +New_VC_Expr
                 (Contract_Case,
                  New_Conditional
                    (Ada_Node    => Contract_Case,
                     Domain      => EW_Pred,
                     Condition   => Enabled,
                     Then_Part   =>
                     +Transform_Expr (Consequence, EW_Pred, Params)),
                  VC_Contract_Case,
                  EW_Pred)));
      end Do_One_Contract_Case;

   --  Start of Compute_Contract_Cases_Exit_Checks

   begin
      Result := New_Void;

      --  If no Contract_Cases on this subprogram, return

      if No (Prag) then
         return;
      end if;

      --  Process individual contract cases

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := First (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));

         --  The "others" choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Others_Contract_Case := Contract_Case;

         --  Regular contract case

         else
            declare
               Guard_Ident : constant W_Identifier_Id := New_Temp_Identifier;
               --  Temporary Why name for the current guard

               --  Whether the current guard is enabled
               Enabled     : constant W_Expr_Id :=
                 New_Relation (Domain   => EW_Term,
                               Op_Type  => EW_Bool,
                               Left     => +Guard_Ident,
                               Op       => EW_Eq,
                               Right    =>
                                 New_Literal (Domain => EW_Term,
                                              Value  => EW_True));
            begin
               Guard_Map.Include (Case_Guard, Guard_Ident);
               Others_Guard := New_Or_Expr (Left   => Others_Guard,
                                            Right  => Enabled,
                                            Domain => EW_Pred);
               Result := Sequence
                 (Result, Do_One_Contract_Case (Contract_Case, Enabled));
            end;
         end if;

         Next (Contract_Case);
      end loop;

      --  A check that contract cases are complete is generated only when there
      --  is no OTHER guard.

      if Present (Others_Contract_Case) then
         declare
            Enabled : constant W_Expr_Id := New_Not (Domain => EW_Pred,
                                                     Right  => Others_Guard);
         begin
            Result := Sequence
              (Result, Do_One_Contract_Case (Others_Contract_Case, Enabled));
         end;
      end if;
   end Compute_Contract_Cases_Exit_Checks;

   ------------------------------------------
   -- Compute_Contract_Cases_Postcondition --
   ------------------------------------------

   --  Pragma/aspect Contract_Cases (Guard1 => Consequence1,
   --                                Guard2 => Consequence2,
   --                                  ...
   --                                GuardN => ConsequenceN
   --                              [,OTHERS => ConsequenceN+1]);

   --  leads to the generation of a postcondition for the corresponding Why
   --  program function.

   --    if guard1 then consequence1
   --    else if guard2 then consequence2
   --    ...
   --    else if guardN then consequenceN
   --    [else consequenceN+1]

   function Compute_Contract_Cases_Postcondition
     (Params : Transformation_Params;
      E      : Entity_Id) return W_Pred_Id
   is
      Prag          : constant Node_Id := Get_Subprogram_Contract_Cases (E);
      Aggr          : Node_Id;
      Contract_Case : Node_Id;
      Case_Guard    : Node_Id;
      Consequence   : Node_Id;

      Result : W_Pred_Id := New_Literal (Value => EW_True);

   --  Start of Compute_Contract_Cases_Postcondition

   begin
      --  If no Contract_Cases on this subprogram, return True

      if No (Prag) then
         return Result;
      end if;

      --  Process individual contract cases in reverse order, to create the
      --  proper if-elsif Why predicate.

      Aggr := Expression (First (Pragma_Argument_Associations (Prag)));
      Contract_Case := Last (Component_Associations (Aggr));
      while Present (Contract_Case) loop
         Case_Guard := First (Choices (Contract_Case));
         Consequence := Expression (Contract_Case);

         --  The "others" choice requires special processing

         if Nkind (Case_Guard) = N_Others_Choice then
            Result := +Transform_Expr (Consequence, EW_Pred, Params);

         --  Regular contract case

         else
            declare
               --  Whether the current guard is enabled in the pre-state

               Enabled : constant W_Expr_Id :=
                 Transform_Attribute_Old (Case_Guard, EW_Pred, Params);
            begin
               Result := New_Conditional
                 (Condition   => Enabled,
                  Then_Part   =>
                    +Transform_Expr (Consequence, EW_Pred, Params),
                  Else_Part   => +Result);
            end;
         end if;

         Prev (Contract_Case);
      end loop;

      return Result;
   end Compute_Contract_Cases_Postcondition;

   ------------------
   -- Compute_Spec --
   ------------------

   function Compute_Spec
     (Params : Transformation_Params;
      E      : Entity_Id;
      Kind   : Name_Id;
      Domain : EW_Domain) return W_Expr_Id
   is
      Cur_Spec : W_Expr_Id := Why_Empty;
      PPC      : Node_Id;
   begin
      PPC := Pre_Post_Conditions (Contract (E));
      while Present (PPC) loop
         if Pragma_Name (PPC) = Kind then
            declare
               Expr : constant Node_Id :=
                 Expression (First (Pragma_Argument_Associations (PPC)));
               Why_Expr : constant W_Expr_Id :=
                 Transform_Expr (Expr, Domain, Params);
            begin
               if Cur_Spec /= Why_Empty then
                  Cur_Spec :=
                    New_And_Then_Expr
                      (Left   => Why_Expr,
                       Right  => Cur_Spec,
                       Domain => Domain);
               else
                  Cur_Spec := Why_Expr;
               end if;
            end;
         end if;

         PPC := Next_Pragma (PPC);
      end loop;

      if Cur_Spec /= Why_Empty then
         return Cur_Spec;
      else
         return New_Literal (Value => EW_True, Domain => Domain);
      end if;
   end Compute_Spec;

   --------------------------------------
   -- Generate_VCs_For_Subprogram_Body --
   --------------------------------------

   procedure Generate_VCs_For_Subprogram_Body
     (File   : in out Why_File;
      E      : Entity_Id)
   is
      Name       : constant String  := Full_Name (E);
      Body_N     : constant Node_Id := SPARK_Util.Get_Subprogram_Body (E);
      Post_N     : constant Node_Id := Get_Location_For_Postcondition (E);
      Pre        : W_Pred_Id;
      Post       : W_Pred_Id;
      Post_Check : W_Prog_Id;
      Params     : Transformation_Params;

      --  Mapping from guards to temporary names, and Why program to check
      --  contract cases on exit.
      Guard_Map      : Ada_To_Why_Ident.Map;
      Contract_Check : W_Prog_Id;

   begin
      --  We open a new theory, so that the context is fresh for that
      --  subprogram

      Open_Theory (File, Name & "__def",
                   Comment =>
                     "Module for checking absence of run-time errors and "
                       & "subprogram contract on subprogram body of "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);
      Current_Subp := E;

      --  First, clear the list of translations for X'Old expressions, and
      --  create a new identifier for F'Result.

      Reset_Map_For_Old;
      Result_Name := New_Result_Temp_Identifier.Id (Name);

      --  Generate code to detect possible run-time errors in the postcondition

      Params := (File        => File.File,
                 Theory      => File.Cur_Theory,
                 Phase       => Generate_VCs_For_Post,
                 Gen_Image   => False,
                 Ref_Allowed => True,
                 Name_Map    => Ada_Ent_To_Why.Empty_Map);

      Compute_Contract_Cases_Exit_Checks
        (Params    => Params,
         E         => E,
         Guard_Map => Guard_Map,
         Result    => Contract_Check);

      Post_Check :=
        Sequence
          (New_Ignore (Prog =>
                       +Compute_Spec (Params, E, Name_Postcondition, EW_Prog)),
           Contract_Check);

      --  Set the phase to Generate_Contract_For_Body from now on, so that
      --  occurrences of F'Result are properly translated as Result_Name.

      Params.Phase := Generate_Contract_For_Body;

      --  Translate contract of E

      Pre  := +Compute_Spec (Params, E, Name_Precondition, EW_Pred);

      Params.Gen_Image := True;
      Post := +Compute_Spec (Params, E, Name_Postcondition, EW_Pred);
      Params.Gen_Image := False;

      --  Set the phase to Generate_VCs_For_Body from now on, so that
      --  occurrences of X'Old are properly translated as reference to the
      --  corresponding binder.

      Params.Phase := Generate_VCs_For_Body;

      --  Declare a global variable to hold the result of a function

      if Ekind (E) = E_Function then
         Emit
           (File.Cur_Theory,
            New_Global_Ref_Declaration
              (Name     => Result_Name,
               Labels =>
                 (1 => New_Identifier
                    (Name =>
                       """GP_Ada_Name:" & Source_Name (E) & "'Result""")),
               Ref_Type => Why_Logic_Type_Of_Ada_Type (Etype (E))));
      end if;

      --  Generate code to detect possible run-time errors in body

      Emit (File.Cur_Theory,
        New_Function_Def
          (Domain  => EW_Prog,
           Name    => To_Ident (WNE_Def),
           Binders => (1 => Unit_Param),
           Labels  =>
             (1 => Cur_Subp_Sloc,
              2 => Cur_Subp_Name),
           Pre     => Pre,
           Post    =>
             +New_VC_Expr (Post_N, +Post, VC_Postcondition, EW_Pred),
           Def     =>
             +Compute_Context
               (Params,
                E,
                Transform_Statements_And_Declarations
                  (Statements
                     (Handled_Statement_Sequence (Body_N))),
              Post_Check,
              Guard_Map)));

      --  We should *not* filter our own entity, it is needed for recursive
      --  calls

      Close_Theory (File, Filter_Entity => Empty);
   end Generate_VCs_For_Subprogram_Body;

   --------------------------------------
   -- Generate_VCs_For_Subprogram_Spec --
   --------------------------------------

   procedure Generate_VCs_For_Subprogram_Spec
     (File : in out Why_File;
      E    : Entity_Id)
   is
      Name    : constant String := Full_Name (E);
      Binders : constant Binder_Array := Compute_Binders (E);
      Params  : Transformation_Params;

      Prog    : W_Prog_Id;

   begin
      Open_Theory (File, Name & "__pre",
                   Comment =>
                     "Module for checking absence of run-time errors and "
                       & "contract cases in the subprogram spec of "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Current_Subp := E;
      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_VCs_For_Pre,
         Gen_Image   => False,
         Ref_Allowed => True,
         Name_Map    => Ada_Ent_To_Why.Empty_Map);

      --  Generate checks for absence of run-time error in the precondition, if
      --  any.

      --  If contract cases are present, generate checks for absence of
      --  run-time errors in guards, and check that contract cases are disjoint
      --  and complete. The completeness is checked in a context where the
      --  precondition is assumed.

      Prog := Sequence
        ((1 => New_Ignore
          (Prog => +Compute_Spec (Params, E, Name_Precondition, EW_Prog)),
          2 => New_Assume_Statement
            (Post => +Compute_Spec (Params, E, Name_Precondition, EW_Pred)),
          3 => Compute_Contract_Cases_Entry_Checks (Params, E)));

      Emit
        (File.Cur_Theory,
         New_Function_Def
           (Domain  => EW_Prog,
            Name    => To_Ident (WNE_Pre_Check),
            Binders => Binders,
            Labels  =>
              (1 => Cur_Subp_Sloc,
               2 => Cur_Subp_Name),
            Def     => +Prog,
            Post    => True_Pred));
      Close_Theory (File, Filter_Entity => E);
   end Generate_VCs_For_Subprogram_Spec;

   ------------------------------------
   -- Get_Location_For_Postcondition --
   ------------------------------------

   function Get_Location_For_Postcondition (E : Entity_Id) return Node_Id is
      PPC  : Node_Id;
      Post : Node_Id := Empty;

   begin
      --  Pre- and postconditions are stored in reverse order in
      --  Pre_Post_Conditions, hence retrieve the last postcondition in this
      --  list to get the first one in source code.

      PPC := Pre_Post_Conditions (Contract (E));
      while Present (PPC) loop
         if Pragma_Name (PPC) = Name_Postcondition then
            Post := Expression (First (Pragma_Argument_Associations (PPC)));
         end if;

         PPC := Next_Pragma (PPC);
      end loop;

      return Post;
   end Get_Location_For_Postcondition;

   ----------------------------------------
   -- Translate_Expression_Function_Body --
   ----------------------------------------

   procedure Translate_Expression_Function_Body
     (File    : in out Why_File;
      E       : Entity_Id;
      In_Body : Boolean)
   is
      Expr_Fun_N         : constant Node_Id := Get_Expression_Function (E);
      pragma Assert (Present (Expr_Fun_N));
      Logic_Func_Binders : constant Binder_Array :=
                             Compute_Logic_Binders (E);
      Logic_Id           : constant W_Identifier_Id :=
                             To_Why_Id (E, Domain => EW_Term, Local => False);
      Read_Names         : constant Name_Set.Set := Get_Reads (E);

      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
        Base_Name & To_String (WNE_Expr_Fun_Axiom);

      Params : Transformation_Params;

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module giving a defining axiom for the "
                       & "expression function "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  If the entity's body is not in SPARK, generate an empty module.

      if not Body_In_SPARK (E) then
         Close_Theory (File, Filter_Entity => Empty);
         return;
      end if;

      --  If the body of the expression function contains aggregates that are
      --  not fully initialized, skip the definition of an axiom for this
      --  expression function.

      if not
        All_Aggregates_Are_Fully_Initialized (Expression (Expr_Fun_N))
      then
         Close_Theory (File, Filter_Entity => Empty);
         return;
      end if;

      Add_Effect_Imports (File, Read_Names);

      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_Logic,
         Gen_Image   => False,
         Ref_Allowed => False,
         Name_Map    => Ada_Ent_To_Why.Empty_Map);

      for Binder of Logic_Func_Binders loop
         declare
            A : constant Node_Id := Binder.Ada_Node;
         begin
            if Present (A) then
               Ada_Ent_To_Why.Insert (Params.Name_Map,
                                      Unique_Entity (A),
                                      +Binder.B_Name);
            else

               --  if there is no Ada_Node, this in a binder generated from
               --  an effect; we add the parameter in the name map using its
               --  unique name

               Ada_Ent_To_Why.Insert
                 (Params.Name_Map,
                  Get_Name_String (Get_Symbol (Binder.B_Name)),
                  +Binder.B_Name);
            end if;
         end;
      end loop;

      --  Given an expression function F with expression E, define an axiom
      --  that states that: "for all <args> => F(<args>) = E".
      --  There is no need to use the precondition here, as the above axiom
      --  is always sound.

      if Etype (E) = Standard_Boolean then
         Emit
           (File.Cur_Theory,
            New_Defining_Bool_Axiom
              (Name    => Logic_Id,
               Binders => Logic_Func_Binders,
               Def     => +Transform_Expr (Expression (Expr_Fun_N),
                                           EW_Pred,
                                           Params)));

      else
         Emit
           (File.Cur_Theory,
            New_Defining_Axiom
              (Name        => Logic_Id,
               Return_Type => Get_EW_Type (Expression (Expr_Fun_N)),
               Binders     => Logic_Func_Binders,
               Def         =>
               +Transform_Expr
                 (Expression (Expr_Fun_N),
                  Expected_Type => EW_Abstract (Etype (E)),
                  Domain        => EW_Term,
                  Params        => Params)));
      end if;

      --  No filtering is necessary here, as the theory should on the contrary
      --  use the previously defined theory for the function declaration. Pass
      --  in the defined entity E so that the graph of dependencies between
      --  expression functions can be built.
      --  Attach the newly created theory as a completion of the existing one.

      Close_Theory (File,
                    Filter_Entity  => Empty,
                    Defined_Entity => E);

      if In_Body then
         Add_Completion (Base_Name, Name, WF_Context_In_Body);
      else
         Add_Completion (Base_Name, Name, WF_Context_In_Spec);
      end if;
   end Translate_Expression_Function_Body;

   -------------------------------
   -- Translate_Subprogram_Spec --
   -------------------------------

   procedure Translate_Subprogram_Spec
     (File : in out Why_File;
      E    : Entity_Id)
   is
      Name         : constant String := Full_Name (E);
      Effects      : W_Effects_Id;
      Logic_Func_Binders : constant Binder_Array :=
                             Compute_Logic_Binders (E);

      Func_Binders : constant Binder_Array := Compute_Binders (E);
      Params       : Transformation_Params;
      Pre          : W_Pred_Id;
      Post         : W_Pred_Id;
      Prog_Id      : constant W_Identifier_Id :=
        To_Why_Id (E, Domain => EW_Prog, Local => True);
   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for declaring a program function (and possibly "
                       & "a logic function) for "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Params :=
        (File        => File.File,
         Theory      => File.Cur_Theory,
         Phase       => Generate_Logic,
         Gen_Image   => False,
         Ref_Allowed => True,
         Name_Map    => Ada_Ent_To_Why.Empty_Map);

      --  We fill the map of parameters, so that in the pre and post, we use
      --  local names of the parameters, instead of the global names

      for Binder of Func_Binders loop
         declare
            A : constant Node_Id := Binder.Ada_Node;
         begin

            --  If the Ada_Node is empty, it's not an interesting binder (e.g.
            --  void_param)

            if Present (A) then
               Ada_Ent_To_Why.Insert (Params.Name_Map,
                                      Unique_Entity (A),
                                      +Binder.B_Name);
            end if;
         end;
      end loop;

      Effects := Compute_Effects (File, E);

      Pre := +Compute_Spec (Params, E, Name_Precondition, EW_Pred);
      Post :=
        +New_And_Expr
          (Left   => +Compute_Spec (Params, E, Name_Postcondition, EW_Pred),
           Right  => +Compute_Contract_Cases_Postcondition (Params, E),
           Domain => EW_Pred);

      if Ekind (E) = E_Function then
         declare
            Logic_Func_Args : constant W_Expr_Array :=
              Compute_Args (E, Logic_Func_Binders);
            Logic_Id        : constant W_Identifier_Id :=
              To_Why_Id (E, Domain => EW_Term, Local => True);

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
                                    Left    => +To_Ident (WNE_Result),
                                    Right   =>
                                    New_Call
                                      (Domain  => EW_Term,
                                       Name    => Logic_Id,
                                       Args    => Logic_Func_Args),
                                    Domain => EW_Pred),
                               Right  => +Post,
                               Domain => EW_Pred);

         begin
            --  Generate a logic function

            Emit
              (File.Cur_Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => Logic_Id,
                  Binders     => Logic_Func_Binders,
                  Return_Type =>
                     +Why_Logic_Type_Of_Ada_Type
                       (Etype (E))));

            Emit
              (File.Cur_Theory,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Id,
                  Binders     => Func_Binders,
                  Return_Type => +Why_Logic_Type_Of_Ada_Type (Etype (E)),
                  Effects     => Effects,
                  Pre         => Pre,
                  Post        => Param_Post));
         end;
      else
         Emit
           (File.Cur_Theory,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => Prog_Id,
               Binders     => Func_Binders,
               Return_Type => New_Base_Type (Base_Type => EW_Unit),
               Effects     => Effects,
               Pre         => Pre,
               Post        => Post));
      end if;
      Close_Theory (File,
                    Filter_Entity  => E,
                    Defined_Entity => E);
   end Translate_Subprogram_Spec;

end Gnat2Why.Subprograms;
