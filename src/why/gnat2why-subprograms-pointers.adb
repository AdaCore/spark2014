------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--           G N A T 2 W H Y - S U B P R O G R A M S - P O I N T E R S      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2020-2023, AdaCore                     --
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

with Ada.Strings.Unbounded;          use Ada.Strings.Unbounded;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Flow_Utility;                   use Flow_Utility;
with GNAT.Source_Info;               use GNAT.Source_Info;
with Gnat2Why.Expr;                  use Gnat2Why.Expr;
with Sinput;                         use Sinput;
with SPARK_Util;                     use SPARK_Util;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
with String_Utils;                   use String_Utils;
with VC_Kinds;                       use VC_Kinds;
with Why.Atree.Accessors;            use Why.Atree.Accessors;
with Why.Atree.Builders;             use Why.Atree.Builders;
with Why.Atree.Modules;              use Why.Atree.Modules;
with Why.Conversions;                use Why.Conversions;
with Why.Gen.Decl;                   use Why.Gen.Decl;
with Why.Gen.Expr;                   use Why.Gen.Expr;
with Why.Gen.Names;                  use Why.Gen.Names;
with Why.Gen.Progs;                  use Why.Gen.Progs;
with Why.Images;                     use Why.Images;
with Why.Inter;                      use Why.Inter;

package body Gnat2Why.Subprograms.Pointers is

   Access_Ids : Ada_To_Why_Ident.Map := Ada_To_Why_Ident.Empty_Map;
   --  Maps Subprogram entities to the Why identifiers for their access

   function Subp_Binder return Binder_Type is
     (Ada_Node => Empty,
      B_Name   => New_Temp_Identifier
        (Typ       => M_Subprogram_Access.Subprogram_Type,
         Base_Name => "subprogram"),
      B_Ent    => Null_Entity_Name,
      Mutable  => False,
      Labels   => Symbol_Sets.Empty_Set);
   --  Binder to be used for the parameter representing the subprogram in calls
   --  through access to subprograms.

   function Check_LSP_For_Subprogram_Access
     (Ada_Node : Node_Id;
      From, To : Entity_Id;
      Params   : Transformation_Params)
      return W_Prog_Id
   with Pre => Present (Ada_Node)
       and then Ekind (From) in Subprogram_Kind | E_Subprogram_Type
       and then Ekind (To) in Subprogram_Kind | E_Subprogram_Type;
   --  Introduce LSP checks to ensure that the contracts of From (if any) are
   --  compatible with those of To. This function expects Result_Name to be
   --  already set and does not perform sandboxing.

   procedure Declare_Theory_For_Access_If_Needed
     (Expr     :     Entity_Id;
      Logic_Id : out W_Identifier_Id)
   with Pre => Nkind (Expr) = N_Attribute_Reference
     and then Nkind (Prefix (Expr)) in N_Has_Entity
     and then Is_Subprogram (Entity (Prefix (Expr)));
   --  Declare a theory containing a logic constant of type __subprogram
   --  standing for the object designated by every access to the prefix of
   --  Expr. If one already exists, none is created. Regardless, Logic_Id is
   --  set to the appropriate logic constant.
   --  Expr is used to dispatch the theory and to store it in E_Module, and
   --  Params is used to store and restore the current theory before the
   --  translation.

   -------------------------------------
   -- Check_LSP_For_Subprogram_Access --
   -------------------------------------

   function Check_LSP_For_Subprogram_Access
     (Ada_Node : Node_Id;
      From, To : Entity_Id;
      Params   : Transformation_Params)
      return W_Prog_Id
   is
      Need_Post_Check  : constant Boolean :=
        not Find_Contracts (To, Pragma_Postcondition).Is_Empty
        or else Present (Get_Pragma (To, Pragma_Contract_Cases));
      --  True if we need to check the compatibility of postconditions

      Need_Pre_Check   : constant Boolean :=
        not Find_Contracts (From, Pragma_Precondition).Is_Empty;
      --  True if we need to check the compatibility of preconditions

   begin
      if not Need_Pre_Check and not Need_Post_Check then
         return +Void;
      end if;

      declare
         To_Pre           : constant W_Pred_Id :=
           +Compute_Spec (Params, To, Pragma_Precondition, EW_Pred);
         To_Post          : W_Pred_Id;
         To_Pre_Assume    : constant W_Prog_Id :=
           New_Assume_Statement (Pred => To_Pre);
         To_Post_RTE      : W_Prog_Id;
         To_Post_Check    : W_Prog_Id;
         From_Pre         : W_Pred_Id;
         From_Pre_Check   : W_Prog_Id;
         From_Post        : W_Pred_Id;
         From_Post_Assume : W_Prog_Id;
         From_Effects     : W_Prog_Id;
         Why_Body         : W_Prog_Id := Sequence
           ((1 => New_Comment
             (Comment => NID ("Assume the precondition of target")),
             2 => To_Pre_Assume));

      begin
         --  If From has a specific precondition, check that it is implied by
         --  the precondition of To.

         if Need_Pre_Check then
            From_Pre :=
              +Compute_Spec (Params, From, Pragma_Precondition, EW_Pred);
            From_Pre_Check := New_Located_Assert
              (Ada_Node => Ada_Node,
               Pred     => From_Pre,
               Reason   => VC_Weaker_Pre_Access,
               Kind     => EW_Assert);

            Why_Body := Sequence
              ((1 => Why_Body,
                2 => New_Comment
                  (Comment => NID ("Check the precondition of source")),
                3 => From_Pre_Check));
         end if;

         --  If To has a specific postcondition, check that it necessarily
         --  evaluates to True after a call to Expr without RTE. Note that
         --  for functions, we may use information coming from the actual
         --  value associated to the result name if there is one.

         if Need_Post_Check then
            To_Post :=
              +New_And_Expr
              (Left   =>
                 +Compute_Spec (Params, To, Pragma_Postcondition, EW_Pred),
               Right  => +Compute_Contract_Cases_Postcondition (Params, To),
               Domain => EW_Pred);
            To_Post_RTE := New_Ignore
              (Ada_Node => Ada_Node,
               Prog     =>
                 +Compute_Spec (Params, To, Pragma_Postcondition, EW_Prog));
            To_Post_Check := New_Located_Assert
              (Ada_Node => Ada_Node,
               Pred     => To_Post,
               Reason   => VC_Stronger_Post_Access,
               Kind     => EW_Assert);
            From_Post :=
              +New_And_Expr
              (Left   =>
                 +Compute_Spec (Params, From, Pragma_Postcondition, EW_Pred),
               Right  => +Compute_Contract_Cases_Postcondition (Params, From),
               Domain => EW_Pred);
            From_Post_Assume :=
              New_Assume_Statement (Pred => From_Post);
            From_Effects :=
              Compute_Call_Effects (Params, From);

            Why_Body := Sequence
              ((1 => Why_Body,
                2 => New_Comment
                  (Comment =>
                     NID ("Simulate the effect of a call to source")),
                3 => From_Effects,
                4 => New_Comment
                  (Comment => NID ("Assume the postcondition of source")),
                5 => From_Post_Assume,
                6 => New_Comment
                  (Comment =>
                     NID ("Check RTE in the postcondition of target")),
                7 => To_Post_RTE,
                8 => New_Comment
                  (Comment => NID ("Check the postcondition of target")),
                9 => To_Post_Check));
         end if;

         Prepend
           (Compute_Dynamic_Property_For_Inputs (Params => Params,
                                                 E      => To),
            Why_Body);

         if Need_Post_Check then
            declare
               Old_Parts : Node_Sets.Set;
            begin
               Collect_Old_For_Subprogram (From, Old_Parts);
               Collect_Old_For_Subprogram (To, Old_Parts);

               Why_Body := +Bind_From_Mapping_In_Expr
                 (Params => Params,
                  Map    => Map_For_Old,
                  Expr   => +Why_Body,
                  Domain => EW_Pterm,
                  Subset => Old_Parts);
            end;
         end if;

         return Why_Body;
      end;
   end Check_LSP_For_Subprogram_Access;

   --------------------------------
   -- Checks_For_Subp_Conversion --
   --------------------------------

   function Checks_For_Subp_Conversion
     (Ada_Node : Entity_Id;
      Expr     : W_Expr_Id := Why_Empty;
      From, To : Entity_Id;
      Params   : Transformation_Params)
      return W_Prog_Id
   is
      From_Access            : constant Boolean := not Is_Subprogram (From);
      From_Profile           : constant Entity_Id :=
        (if From_Access then Directly_Designated_Type (From) else From);
      From_Ent               : constant Entity_Id :=
        (if From_Access
         and then Present (Access_Subprogram_Wrapper (From_Profile))
         then Access_Subprogram_Wrapper (From_Profile)
         else From_Profile);
      To_Profile             : constant Entity_Id :=
        Directly_Designated_Type (To);
      To_Ent                 : constant Entity_Id :=
        (if Present (Access_Subprogram_Wrapper (To_Profile))
         then Access_Subprogram_Wrapper (To_Profile)
         else To_Profile);
      From_Formals           : constant Item_Array :=
        Compute_Subprogram_Parameters (From_Ent, EW_Prog);
      To_Formals             : constant Item_Array (From_Formals'Range) :=
        Compute_Subprogram_Parameters (To_Ent, EW_Prog);
      To_Effects             : Item_Array :=
        Compute_Binders_For_Effects (To_Ent);
      Checks                 : W_Prog_Id;

      --  As this check can occur anywhere during the translation, we need to
      --  preserve the result name.

      Save_Result_Is_Mutable : constant Boolean := Result_Is_Mutable;
      Save_Result_Name       : constant W_Identifier_Id := Result_Name;

   begin
      if From_Profile = To_Profile then
         return +Void;
      end if;

      --  To check LSP, we will need to emulate effect of a call to Expr. For
      --  that, we need to "sandbox" the check:
      --    * We introduce local names for formals parameters of the source
      --      subprogram type and bind them in the local environement.
      --    * As the contracts of the source and the target of the conversion
      --      refer to different formal entities, we also need to bind the
      --      names of the formals parameters of the target subprogram type to
      --      the local names used for those of the source.
      --    * We introduce local names for variable parts of global objects
      --      accessed by the target and bind them too.
      --    * Because of LSP, variables accessed by the source shall be a
      --      subset of those accessed by the target. For specialized
      --      actuals, LSP is not ensured but we do not need to sandbox
      --      globals as they cannot be modified.
      --  ??? The sandboxing of global effect cannot be used yet as function
      --  pointers cannot be annotated with Global contracts currently.

      pragma Assert
        (if Is_Specialized_Actual (Ada_Node, Specialized_Call_Params)
         then To_Effects'Length = 0);

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);
      Localize_Binders (To_Effects);
      Push_Binders_To_Symbol_Table (From_Formals);
      Push_Binders_To_Symbol_Table (To_Effects);

      --  Go over formal parameters of From and map those of To to the same
      --  binders.

      for I in From_Formals'Range loop
         declare
            B    : Item_Type renames To_Formals (I);
            Node : constant Node_Id := Get_Ada_Node_From_Item (B);
         begin
            if Present (Node) then
               Ada_Ent_To_Why.Insert (Symbol_Table,
                                      Node,
                                      From_Formals (I));
            end if;
         end;
      end loop;

      --  For functions, we need an identifier for the result of the call

      if Is_Function_Type (To_Profile) then
         Result_Is_Mutable := False;
         Result_Name :=
           New_Temp_Identifier
             (Base_Name => "result",
              Typ       => Type_Of_Node (To_Profile));
      end if;

      Checks := Check_LSP_For_Subprogram_Access
        (Ada_Node => Ada_Node,
         From     => From_Ent,
         To       => To_Ent,
         Params   => Params);

      --  Bind the identifier for the result of the call. We could leave it
      --  undefined, as we assume the postcondition of the source subprogram
      --  during checking of LSP. We map it to a call to the actual converted
      --  function. We use a direct call if From_Access is False:
      --
      --    let result = <from_ent> ... in ...
      --
      --  and an indirect call to the value of Expr otherwise:
      --
      --    let result = __call <Expr>.__rec_value ... in ...
      --
      --  This allows to use previous knowledge about the behavior of Expr to
      --  prove the postcondition of functions (eg. if Expr was created as
      --  the 'Access attribute of a function with a precise postcondition).

      if Is_Function_Type (To_Profile) then
         declare
            Subp_Value   : constant W_Expr_Array :=
              (if not From_Access then (1 .. 0 => <>)
               else (1 => New_Subprogram_Value_Access
                     (Ada_Node => Ada_Node,
                      Expr     => Expr,
                      Domain   => EW_Pterm)));
            --  We compute the access in the Pterm domain as we don't want to
            --  generate a dereference check here. This code will be protected
            --  by a conditional making sure that Expr is not null here.

            From_Effects : constant Item_Array :=
              Compute_Binders_For_Effects (From_Ent);
            Formal_Args  : constant W_Expr_Array :=
              (if From_Formals'Length = 0 and From_Effects'Length = 0
               then (1 => +Void)
               else Get_Args_From_Binders
                 (To_Binder_Array (From_Formals & From_Effects),
                  Ref_Allowed => Params.Ref_Allowed));
            Call_Id      : constant W_Identifier_Id :=
              (if From_Access then Get_Logic_Function (To_Profile)
               else To_Why_Id (From_Ent, Domain => EW_Pterm));
            Need_Guard   : constant Boolean :=
              (if From_Access then Use_Guard_For_Function (To_Profile)
               else Use_Guard_For_Function (From_Ent));
            Guard_Id     : constant W_Identifier_Id :=
              (if From_Access then Get_Logic_Function_Guard (To_Profile)
               else Guard_Predicate_Name (From_Ent));

         begin
            if Need_Guard then
               Checks := Sequence
                 (Ada_Node => Ada_Node,
                  Left     => New_Assume_Statement
                    (Ada_Node => Ada_Node,
                     Pred     => New_Call
                       (Name => Guard_Id,
                        Args => (1 => +Result_Name) & Subp_Value & Formal_Args,
                        Typ  => Get_Typ (Result_Name))),
                  Right    => Checks);
            end if;

            Checks := New_Binding
              (Ada_Node => Ada_Node,
               Name     => Result_Name,
               Def      => +W_Expr_Id'(New_Call
                 (Domain  => EW_Pterm,
                  Name    => Call_Id,
                  Args    => Subp_Value & Formal_Args,
                  Typ     => Get_Typ (Result_Name))),
               Context  => Checks,
               Typ      => EW_Unit_Type);

            --  Restore the result name

            Result_Is_Mutable := Save_Result_Is_Mutable;
            Result_Name := Save_Result_Name;
         end;
      end if;

      --  Map both constant and mutable parts of Formals

      for Binder of To_Binder_Array (From_Formals) loop
         if Binder.Mutable then
            Checks := New_Binding_Ref
              (Ada_Node => Ada_Node,
               Name     => Binder.B_Name,
               Def      => New_Any_Expr
                 (Return_Type => Get_Typ (Binder.B_Name),
                  Labels      => Symbol_Sets.Empty_Set),
               Context  => Checks,
               Typ      => EW_Unit_Type);
         else
            Checks := New_Binding
              (Ada_Node => Ada_Node,
               Name     => Binder.B_Name,
               Def      => New_Any_Expr
                 (Return_Type => Get_Typ (Binder.B_Name),
                  Labels      => Symbol_Sets.Empty_Set),
               Context  => Checks,
               Typ      => EW_Unit_Type);
         end if;
      end loop;

      --  Map mutable parts of To_Effects only

      for Binder of To_Binder_Array (To_Effects) loop
         if Binder.Mutable then
            Checks := New_Binding_Ref
              (Ada_Node => Ada_Node,
               Name     => Binder.B_Name,
               Def      => New_Any_Expr
                 (Return_Type => Get_Typ (Binder.B_Name),
                  Labels      => Symbol_Sets.Empty_Set),
               Context  => Checks,
               Typ      => EW_Unit_Type);
         end if;
      end loop;

      Checks := New_Ignore
        (Ada_Node => Ada_Node,
         Prog     => Checks);

      --  Only do the check if Expr is not null

      if From_Access then
         Checks := New_Conditional
           (Condition => New_Not
              (Right  => New_Record_Access
                   (Name  => +Expr,
                    Field => M_Subprogram_Access.Rec_Is_Null,
                    Typ   => EW_Bool_Type)),
            Then_Part => Checks,
            Typ       => EW_Unit_Type);
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      return Checks;
   end Checks_For_Subp_Conversion;

   ----------------------------------------
   -- Complete_Access_To_Subprogram_Type --
   ----------------------------------------

   procedure Complete_Access_To_Subprogram_Type
     (Th : Theory_UC;
      E  : Access_Kind_Id)
   is
      Spec_Binders       : constant Binder_Array :=
        Binder_Array'(1 => Subp_Binder);
      Profile            : constant Entity_Id := Directly_Designated_Type (E);
      Has_Wrapper        : constant Boolean :=
        Present (Access_Subprogram_Wrapper (Profile));
      Profile_Or_Wrapper : constant Entity_Id :=
        (if Has_Wrapper then Access_Subprogram_Wrapper (Profile)
         else Profile);
      --  Use the wrapper if any to get the contracts

      Use_Result_Name    : constant Boolean := Is_Function_Type (Profile)
        and then Has_Wrapper;
      --  We need to set the result name only on functions which have a
      --  contract.

   begin
      if Use_Result_Name then
         Result_Name := New_Result_Ident (Type_Of_Node (Profile));
         Result_Is_Mutable := False;
      end if;

      --  Generate a program function for calling the designated subprogram

      Generate_Subprogram_Program_Fun
        (Th                     => Th,
         E                      => Profile_Or_Wrapper,
         Prog_Id                => To_Local (E_Symb (E, WNE_Pointer_Call)),
         Spec_Binders           => Spec_Binders,
         Is_Access_Subp_Wrapper => Has_Wrapper);

      --  Generate an axiom for the contract of E if it is a function. As the
      --  logic function of access-to-subprogram types is shared between all
      --  types with the same profile, the axiom should be guarded by the range
      --  predicate of the type.

      Generate_Axiom_For_Post
        (Th                     => Th,
         E                      => Profile_Or_Wrapper,
         Spec_Binders           => Spec_Binders,
         Spec_Guard             => +New_Call
           (Domain  => EW_Pred,
            Name    => E_Symb (E, WNE_Range_Pred),
            Binders => Spec_Binders,
            Typ     => EW_Bool_Type),
         Is_Access_Subp_Wrapper => Has_Wrapper);

      if Use_Result_Name then
         Result_Name := Why_Empty;
         Result_Is_Mutable := False;
      end if;
   end Complete_Access_To_Subprogram_Type;

   ---------------------------------------------------
   -- Create_Theory_For_HO_Specialization_If_Needed --
   ---------------------------------------------------

   procedure Create_Theory_For_HO_Specialization_If_Needed (Call : Node_Id) is
      Specialized_Call_Params_Save : constant Node_Maps.Map :=
        Specialized_Call_Params;
      Result_Name_Save             : constant W_Identifier_Id := Result_Name;
      Result_Is_Mutable_Save       : constant Boolean := Result_Is_Mutable;
      Theory_Name                  : constant Symbol :=
        Get_Specialized_Function_Theory_Name (Call);
      Module                       : constant W_Module_Id := New_Module
        (File => No_Symbol,
         Name => Img (Theory_Name));
      Ax_Module                    : constant W_Module_Id := New_Module
        (File => No_Symbol,
         Name => Img (Theory_Name) & To_String (WNE_Axiom_Suffix));
      Caller                       : constant Entity_Id :=
        Get_Called_Entity_For_Proof (Call);
      Rec_Ax_Module                : constant W_Module_Id :=
        (if Is_Recursive (Caller)
         then New_Module
           (File => No_Symbol,
            Name => Img (Theory_Name) & "__rec_axioms")
         else Why_Empty);
      Fun_Name                     : constant String := Short_Name (Caller);
      Fun_Typ                      : constant W_Type_Id :=
        Type_Of_Node (Caller);
      Fun_Id                       : constant W_Identifier_Id :=
        New_Identifier
          (Domain => EW_Term,
           Symb   => NID (Fun_Name),
           Typ    => Fun_Typ,
           Module => Module);
      Prog_Id                      : constant W_Identifier_Id :=
        New_Identifier
          (Domain => EW_Prog,
           Symb   => NID (Fun_Name),
           Typ    => Fun_Typ,
           Module => Ax_Module);
      Guard_Id                     : constant W_Identifier_Id :=
        New_Identifier
          (Domain => EW_Pred,
           Symb   => NID (Fun_Name & "__" & Function_Guard),
           Module => Module);
      More_Globals                 : Flow_Types.Flow_Id_Sets.Set;
      Th                           : Theory_UC;
      Position                     : Node_Id_HO_Specializations_Map.Cursor;
      Inserted                     : Boolean;

   begin
      M_HO_Specializations.Insert
        (Caller, Name_Id_HO_Specializations_Map.Empty_Map, Position, Inserted);

      if M_HO_Specializations (Position).Contains (Key => Theory_Name) then
         return;
      end if;

      --  Populate the M_HO_Specializations map

      M_HO_Specializations (Position).Insert
        (Theory_Name,
         M_HO_Specialization_Type'(Module        => Module,
                                   Ax_Module     => Ax_Module,
                                   Rec_Ax_Module => Rec_Ax_Module,
                                   Guard_Id      => Guard_Id,
                                   Prog_Id       => Prog_Id,
                                   Fun_Id        => Fun_Id));

      --  Generate the logic function declarations

      Th :=
        Open_Theory
          (WF_Context, Module,
           Comment =>
             "Module for declaring a specialized logic function symbol for"
           & " the call to a function with higher order specialization at "
           & (if Sloc (Call) > 0 then
                Build_Location_String (Sloc (Call))
             else "<no location>")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Store the specialized parameters in the global
      --  Specialized_Call_Params map.

      Specialized_Call_Params := Get_Specialized_Parameters
        (Call, Specialized_Call_Params);
      More_Globals := Get_Globals_From_Specialized_Parameters
        (Specialized_Call_Params);

      Declare_Logic_Functions
        (Th                    => Th,
         E                     => Caller,
         Specialization_Module => Theory_Name,
         More_Reads            => More_Globals);

      Close_Theory (Th,
                    Kind => Definition_Theory);

      --  Generate a module containing a program function and an axiom for the
      --  specialization.

      Th :=
        Open_Theory
          (WF_Context, Ax_Module,
           Comment =>
             "Module for generating a specialized program function symbol and"
           & " possibly an axiom for the call to a function with higher order"
           & " specialization at "
           & (if Sloc (Call) > 0 then
                Build_Location_String (Sloc (Call))
             else "<no location>")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Result_Name := New_Result_Ident (Fun_Typ);
      Result_Is_Mutable := False;

      Generate_Subprogram_Program_Fun
        (Th                    => Th,
         E                     => Caller,
         Prog_Id               => To_Local (Prog_Id),
         Specialization_Module => Theory_Name,
         More_Reads            => More_Globals);

      Generate_Axiom_For_Post
        (Th                    => Th,
         E                     => Caller,
         Specialization_Module => Theory_Name,
         More_Reads            => More_Globals);

      Close_Theory (Th,
                    Kind => Definition_Theory);

      Record_Extra_Dependency
        (Defining_Module => Module,
         Axiom_Module    => Ax_Module);

      --  Restore the state

      Result_Name := Result_Name_Save;
      Result_Is_Mutable := Result_Is_Mutable_Save;
      Specialized_Call_Params := Specialized_Call_Params_Save;
   end Create_Theory_For_HO_Specialization_If_Needed;

   -----------------------------------------
   -- Create_Theory_For_Profile_If_Needed --
   -----------------------------------------

   procedure Create_Theory_For_Profile_If_Needed (E : Access_Kind_Id) is
      Profile : constant Entity_Id := Directly_Designated_Type (E);
      Name    : constant Symbol := Get_Profile_Theory_Name (Profile);
      Module  : constant W_Module_Id := New_Module
        (File => No_Symbol,
         Name => Img (Name));

      Th : Theory_UC;
   begin
      if M_Subprogram_Profiles.Contains (Key => Name) then
         return;
      end if;

      Th :=
        Open_Theory
          (WF_Context, Module,
           Comment =>
             "Module for possibly declaring a call function associated to"
           & "function profiles designated by type "
           & """" & Get_Name_String (Chars (E)) & """"
           & (if Sloc (E) > 0 then
                " defined at " & Build_Location_String (Sloc (E))
             else "")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  For functions, declare a __call logic function and a pred_call
      --  predicate which can be used for axiom guards.

      if Is_Function_Type (Profile) then
         declare
            Call_Id : constant W_Identifier_Id := New_Identifier
              (Domain => EW_Term,
               Name   => New_Name
                 (Symb      => NID ("__call"),
                  Module    => Module),
               Typ    => Type_Of_Node (Etype (Profile)));
            Pred_Id : constant W_Identifier_Id := New_Identifier
              (Domain => EW_Term,
               Symb   => NID ("pred_call"),
               Module => Module,
               Typ    => EW_Bool_Type);
         begin
            M_Subprogram_Profiles.Insert
              (Name, M_Subprogram_Profile_Type'(Is_Function => True,
                                                Call_Id     => Call_Id,
                                                Pred_Id     => Pred_Id,
                                                Module      => Module));

            Declare_Logic_Functions
              (Th           => Th,
               E            => Profile,
               Spec_Binders => Binder_Array'(1 => Subp_Binder));
         end;

      --  For procedure, the module is currently empty.
      --  ??? We could declare a post predicate symbol like we do for
      --  dispatching calls if we want to track the postcondition of
      --  procedure calls more precisely through 'Access and conversions.

      else
         M_Subprogram_Profiles.Insert
           (Name, M_Subprogram_Profile_Type'(Is_Function => False,
                                             Module      => Module));
      end if;

      Close_Theory (Th, Kind => Definition_Theory);
   end Create_Theory_For_Profile_If_Needed;

   ---------------------------------------
   -- Declare_Access_To_Subprogram_Type --
   ---------------------------------------

   procedure Declare_Access_To_Subprogram_Type
     (Th : Theory_UC;
      E  : Access_Kind_Id)
   is
   begin
      --  Export the theory containing the pointer record definition.

      Add_With_Clause (Th, M_Subprogram_Access.Module, EW_Export);

      --  Rename the representative record type as expected.

      Emit (Th, New_Type_Decl (Name  => To_Why_Type (E, Local => True),
                               Alias => +New_Named_Type
                                 (Name => To_Name (WNE_Rec_Rep))));
      Emit
        (Th,
         Why.Atree.Builders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (E_Symb (E, WNE_Dummy)),
            Binders     => (1 .. 0 => <>),
            Labels      => Symbol_Sets.Empty_Set,
            Location    => No_Location,
            Return_Type =>
              +New_Named_Type (Name => To_Why_Type (E, Local => True))));

      --  Declare a predicate symbol for the range predicate of the pointer
      --  type. This predicate is used to express that an access-to-subprogram
      --  object is compatible with the contract of the type. Currently, the
      --  predicate of access to function types is axiomatized in the
      --  completion module while the predicate of access to procedures is
      --  simply True, as we don't need it since we don't generate axioms for
      --  procedures.

      Emit
        (Th,
         Why.Gen.Binders.New_Function_Decl
           (Domain   => EW_Pred,
            Name     => To_Local (E_Symb (E, WNE_Range_Pred)),
            Binders  => (1 => Subp_Binder),
            Labels   => Symbol_Sets.Empty_Set,
            Def      =>
              (if Is_Function_Type (Directly_Designated_Type (E))
               then Why_Empty
               else +True_Pred),
            Location => No_Location));

      --  Associate call identifiers to the designated profile in the symbol
      --  table. They will be queried when translating calls through
      --  access-to-subprograms (Get_Called_Entity returns the profile on
      --  these calls).

      declare
         Profile : constant Entity_Id := Directly_Designated_Type (E);
      begin
         if Ada_Ent_To_Why.Has_Element (Symbol_Table, Profile) then
            pragma Assert (not Is_Base_Type (E));
         elsif Is_Function_Type (Profile) then
            Insert_Item
              (Profile,
               Item_Type'(Func,
                 Local     => False,
                 Init      => <>,
                 For_Logic => (Ada_Node => Profile,
                               B_Name   => Get_Logic_Function (Profile),
                               B_Ent    => Null_Entity_Name,
                               Mutable  => False,
                               Labels   => <>),
                 For_Prog  => (Ada_Node => Profile,
                               B_Name   => E_Symb (E, WNE_Pointer_Call),
                               B_Ent    => Null_Entity_Name,
                               Mutable  => False,
                               Labels   => <>)));
         else
            Insert_Tmp_Item_For_Entity
              (Profile,
               E_Symb (E, WNE_Pointer_Call),
               Mutable => False);
         end if;
      end;
   end Declare_Access_To_Subprogram_Type;

   -----------------------------------------
   -- Declare_Theory_For_Access_If_Needed --
   -----------------------------------------

   procedure Declare_Theory_For_Access_If_Needed
     (Expr     :    Entity_Id;
      Logic_Id : out W_Identifier_Id)
   is
      Subp          : constant Entity_Id :=
        Entity (Prefix (Expr));
      Name          : constant String :=
        Get_Module_Name (E_Module (Subp)) & "__" & To_String (WNE_Attr_Access);
      Module        : constant W_Module_Id :=
        New_Module
          (Ada_Node => Expr,
           File     => No_Symbol,
           Name     => Name);

      --  Select files for the declaration and axiom

      Position : Ada_To_Why_Ident.Cursor;
      Inserted : Boolean;
      Th       : Theory_UC;

   begin
      Logic_Id :=
        New_Identifier
          (Name   => New_Name
             (Symb   => NID (To_String (WNE_Attr_Access)),
              Module => Module),
           Domain => EW_Pterm,
           Typ    => M_Subprogram_Access.Subprogram_Type);

      --  Try to insert the new identifier in the Access_Ids map

      Access_Ids.Insert
        (Key      => Subp,
         New_Item => Logic_Id,
         Position => Position,
         Inserted => Inserted);

      --  If it was already present, return the already declared symbol

      if not Inserted then
         Logic_Id := Ada_To_Why_Ident.Element (Position);
         return;
      end if;

      --  Otherwise, declare the new symbol.
      --  Insert new modules for the logic function in the module map

      Insert_Extra_Module (Expr, Module);
      Insert_Extra_Module
        (Expr,
         New_Module (File => No_Symbol,
                     Name => Name & To_String (WNE_Axiom_Suffix)),
         Is_Axiom => True);

      --  Generate the logic constant declaration

      Th :=
        Open_Theory
          (WF_Context, E_Module (Expr),
           Comment =>
             "Module for declaring an abstract constant for the subprogram"
           & " Access attribute at "
           & (if Sloc (Expr) > 0 then
                Build_Location_String (Sloc (Expr))
             else "<no location>")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (Logic_Id),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => M_Subprogram_Access.Subprogram_Type));

      Close_Theory (Th,
                    Kind           => Definition_Theory,
                    Defined_Entity => Expr);

      Th :=
        Open_Theory
          (WF_Context, E_Axiom_Module (Expr),
           Comment =>
             "Module for defining the value of the subprogram Access"
           & " attribute at "
           & (if Sloc (Expr) > 0 then
                Build_Location_String (Sloc (Expr))
             else "<no location>")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  For functions, generate the axiom in a completion module. It states
      --  that __call and pred_call match the specific symbols for the Subp.

      if Ekind (Subp) = E_Function then
         declare
            Why_Type     : constant W_Type_Id :=
              Type_Of_Node (Etype (Subp));
            Binders      : constant Item_Array := Compute_Subprogram_Parameters
              (Subp, EW_Term);
            Args         : constant W_Expr_Array :=
              (if Binders'Length = 0 then (1 => +Void)
               else Get_Args_From_Binders
                 (To_Binder_Array (Binders), Ref_Allowed => False));
            Id           : constant W_Identifier_Id :=
              To_Why_Id (Subp, Domain => EW_Term);
            Call_Eq      : constant W_Pred_Id := +New_Comparison
              (Symbol => Why_Eq,
               Left   => New_Call
                 (Domain => EW_Term,
                  Name   => Id,
                  Args   => Args,
                  Typ    => Why_Type),
               Right  => New_Call
                 (Domain => EW_Term,
                  Name   => Get_Logic_Function
                    (Directly_Designated_Type (Etype (Expr))),
                  Args   => +Logic_Id & Args,
                  Typ    => Why_Type),
               Domain => EW_Pred);
            Result_Ident : constant W_Identifier_Id := New_Temp_Identifier
              (Typ       => Why_Type,
               Base_Name => "result");
            Guard_Id     : constant W_Identifier_Id :=
              Get_Logic_Function_Guard
                (Directly_Designated_Type (Etype (Expr)));
            Pred_Eq      : constant W_Pred_Id := New_Connection
              (Left  => New_Call
                 (Name   => Guard_Predicate_Name (Subp),
                  Args   => (1 => +Result_Ident) & Args,
                  Typ    => EW_Bool_Type),
               Right => New_Call
                 (Name   => Guard_Id,
                  Args   => (1 => +Result_Ident, 2 => +Logic_Id) & Args,
                  Typ    => EW_Bool_Type),
               Op    => EW_Equivalent);
         begin

            --  ??? adding a dependency annotation on this axiom on Id results
            --  in unproved checks

            Emit (Th,
                  New_Guarded_Axiom
                    (Name     => NID (Def_Axiom),
                     Binders  => To_Binder_Array (Binders),
                     Def      => Call_Eq,
                     Dep      =>
                       New_Axiom_Dep
                         (Name => Get_Logic_Function
                              (Directly_Designated_Type (Etype (Expr))),
                          Kind => EW_Axdep_Func)));

            Emit (Th,
                  New_Guarded_Axiom
                    (Name     => NID
                       (Def_Axiom & "__" & Function_Guard),
                     Binders  =>
                       Binder_Type'(Ada_Node  => Empty,
                                    B_Name    => +Result_Ident,
                                    B_Ent     => Null_Entity_Name,
                                    Mutable   => False,
                                    Labels    => <>)
                     & To_Binder_Array (Binders),
                     Def      => Pred_Eq,
                     Dep      => New_Axiom_Dep (Name => Guard_Id,
                                                Kind => EW_Axdep_Pred)));
         end;
      end if;

      Close_Theory (Th,
                    Kind           => Axiom_Theory,
                    Defined_Entity => Expr);

   end Declare_Theory_For_Access_If_Needed;

   ---------------------------------------------
   -- Get_Globals_From_Specialized_Parameters --
   ---------------------------------------------

   function Get_Globals_From_Specialized_Parameters
     (Params : Node_Maps.Map) return Flow_Types.Flow_Id_Sets.Set
   is
      Read_Ids : Flow_Types.Flow_Id_Sets.Set;
   begin
      for Actual of Params loop
         declare
            Local_Reads  : Flow_Types.Flow_Id_Sets.Set;
            Local_Writes : Flow_Types.Flow_Id_Sets.Set;

         begin
            --  Collect global variables potentially read and written

            Flow_Utility.Get_Proof_Globals (Subprogram      => Actual,
                                            Reads           => Local_Reads,
                                            Writes          => Local_Writes,
                                            Erase_Constants => True);
            pragma Assert (Local_Writes.Is_Empty);

            Read_Ids.Union (Local_Reads);
         end;
      end loop;

      return Read_Ids;
   end Get_Globals_From_Specialized_Parameters;

   ------------------------------------------
   -- Get_Specialized_Function_Theory_Name --
   ------------------------------------------

   function Get_Specialized_Function_Theory_Name
     (Call : Node_Id) return Symbol
   is
      Name   : Unbounded_String :=
        To_Unbounded_String ("Higher_order_spec");
      Caller : constant Entity_Id := Get_Called_Entity_For_Proof (Call);

      procedure Append_Param_To_Name (Formal : Entity_Id; Actual : Node_Id);
      --  For each parameter which might be specialized in Call, add the name
      --  of the specialized actual to Name if it is specialized and the
      --  string "none" otherwise.

      --------------------------
      -- Append_Param_To_Name --
      --------------------------

      procedure Append_Param_To_Name (Formal : Entity_Id; Actual : Node_Id) is
      begin
         if Is_Specializable_Formal (Formal) then
            if Is_Access_Attribute_Of_Function (Actual) then
               declare
                  Callee : constant Entity_Id := Entity (Prefix (Actual));
               begin
                  Name := Name & "__" & Capitalize_First (Full_Name (Callee));
               end;
            elsif Nkind (Actual) in N_Identifier | N_Expanded_Name
              and then Specialized_Call_Params.Contains (Entity (Actual))
            then
               declare
                  Callee : constant Entity_Id :=
                    Specialized_Call_Params.Element (Entity (Actual));
               begin
                  Name := Name & "__" & Capitalize_First (Full_Name (Callee));
               end;
            else
               pragma Assert (not Is_Specialized_Actual (Actual));
               Name := Name & "__none";
            end if;
         end if;
      end Append_Param_To_Name;

      procedure Append_Params is new Iterate_Call_Parameters
        (Append_Param_To_Name);
   begin
      --  Add the name of the caller to name

      Name := Name & "__" & Capitalize_First (Full_Name (Caller));

      --  Add the specialized parameters

      Append_Params (Call);

      return NID (To_String (Name));
   end Get_Specialized_Function_Theory_Name;

   -----------------------------------------
   -- New_Dynamic_Property_For_Subprogram --
   -----------------------------------------

   function New_Dynamic_Property_For_Subprogram
     (Ty     : Access_Kind_Id;
      Expr   : W_Term_Id;
      Params : Transformation_Params)
      return W_Pred_Id
   is (New_Conditional
         (Condition   => New_Not
            (Right  => Pred_Of_Boolean_Term
               (W => New_Record_Access
                    (Name  => Expr,
                     Field => M_Subprogram_Access.Rec_Is_Null,
                     Typ   => EW_Bool_Type))),
          Then_Part   => New_Call
            (Name   => E_Symb (Ty, WNE_Range_Pred),
             Args   => (1 => +New_Record_Access
                        (Name  => Expr,
                         Field => M_Subprogram_Access.Rec_Value,
                         Typ   => M_Subprogram_Access.Subprogram_Type)),
             Typ    => EW_Bool_Type)));
   --  Use the range predicate to express that Expr has the contract of its
   --  type if it is not null.

   ---------------------------------
   -- New_Subprogram_Value_Access --
   ---------------------------------

   function New_Subprogram_Value_Access
     (Ada_Node : Entity_Id := Empty;
      Expr     : W_Expr_Id;
      Domain   : EW_Domain) return W_Expr_Id
   is (if Domain = EW_Prog
       then +New_VC_Call (Ada_Node => Ada_Node,
                          Name     => M_Subprogram_Access.Rec_Value_Prog,
                          Progs    => (1 => Expr),
                          Reason   => VC_Null_Pointer_Dereference,
                          Typ      => M_Subprogram_Access.Subprogram_Type)
       else New_Record_Access
         (Ada_Node => Ada_Node,
          Name     => Expr,
          Field    => M_Subprogram_Access.Rec_Value,
          Typ      => M_Subprogram_Access.Subprogram_Type));

   ----------------------------------------------
   -- Transform_Access_Attribute_Of_Subprogram --
   ----------------------------------------------

   function Transform_Access_Attribute_Of_Subprogram
     (Expr   : N_Attribute_Reference_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Id
   is
      Logic_Id : W_Identifier_Id;
      Subp     : constant Entity_Id := Entity (Prefix (Expr));
      T        : W_Expr_Id;

      procedure Check_No_Globals with Ghost;
      --  Ghost procedure which checks that Subp has no global state.
      --  We use it to ease debugging while flow analysis does not reject
      --  this case.

      ----------------------
      -- Check_No_Globals --
      ----------------------

      procedure Check_No_Globals is
         Reads  : Flow_Id_Sets.Set;
         Writes : Flow_Id_Sets.Set;
      begin
         Get_Proof_Globals
           (Subprogram      => Subp,
            Reads           => Reads,
            Writes          => Writes,
            Erase_Constants => False);
         pragma Assert (Writes.Is_Empty and Reads.Is_Empty);
         --  If we stop here, it means that Subp has some global state,
         --  which is not supported in SPARK.
      end Check_No_Globals;

   --  Start of processing for Transform_Access_Attribute_Of_Subprogram

   begin
      Check_No_Globals;

      --  Declare a logic symbol for the subprogram object designated by Expr
      --  if needed.

      Declare_Theory_For_Access_If_Needed (Expr, Logic_Id);

      --  Construct a pointer value from the subprogram logic object

      T := New_Record_Aggregate
        (Ada_Node     => Expr,
         Associations =>
           (1 => New_Field_Association
                (Domain => Domain,
                 Field  => M_Subprogram_Access.Rec_Is_Null,
                 Value  => Bool_False (Domain)),
            2 => New_Field_Association
              (Domain => Domain,
               Field  => M_Subprogram_Access.Rec_Value,
               Value  => +Logic_Id)),
         Typ          => EW_Abstract (Etype (Expr)));

      --  In the program domain, we need to perform checks on conversions.
      --  Liskov checks need to be introduced manually so that they are done
      --  with respect to the prefix of the attribute. Other checks (null
      --  exclusion and predicates) are handled through the usual conversion
      --  mechanism.

      if Domain = EW_Prog then
         T := +Sequence
           (Ada_Node => Expr,
            Left     => Checks_For_Subp_Conversion
              (Ada_Node => Expr,
               From     => Subp,
               To       => Etype (Expr),
               Params   => Params),
            Right    => +T);

         T := Insert_Subp_Pointer_Conversion
           (Ada_Node   => Expr,
            Domain     => EW_Prog,
            Expr       => T,
            To         => EW_Abstract (Etype (Expr)),
            Need_Check => True);
      end if;

      return T;
   end Transform_Access_Attribute_Of_Subprogram;

end Gnat2Why.Subprograms.Pointers;
