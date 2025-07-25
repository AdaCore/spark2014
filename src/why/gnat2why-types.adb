------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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
with Ada.Strings.Unbounded;         use Ada.Strings.Unbounded;
with Ada.Text_IO;  --  For debugging, to print info before raising an exception
with Common_Containers;             use Common_Containers;
with Flow_Types;                    use Flow_Types;
with GNAT.Source_Info;
with GNATCOLL.Symbols;              use GNATCOLL.Symbols;
with Gnat2Why.Error_Messages;       use Gnat2Why.Error_Messages;
with Gnat2Why.Expr;                 use Gnat2Why.Expr;
with Gnat2Why.Expr.Aggregates;      use Gnat2Why.Expr.Aggregates;
with Gnat2Why.Subprograms;          use Gnat2Why.Subprograms;
with Gnat2Why.Subprograms.Pointers; use Gnat2Why.Subprograms.Pointers;
with Gnat2Why.Tables;               use Gnat2Why.Tables;
with Gnat2Why.Util;                 use Gnat2Why.Util;
with Namet;                         use Namet;
with Sinput;                        use Sinput;
with Snames;                        use Snames;
with SPARK_Atree;                   use SPARK_Atree;
with SPARK_Definition;              use SPARK_Definition;
with SPARK_Definition.Annotate;     use SPARK_Definition.Annotate;
with SPARK_Util;                    use SPARK_Util;
with SPARK_Util.Hardcoded;          use SPARK_Util.Hardcoded;
with SPARK_Util.Subprograms;        use SPARK_Util.Subprograms;
with SPARK_Util.Types;              use SPARK_Util.Types;
with Stand;                         use Stand;
with Types;                         use Types;
with VC_Kinds;                      use VC_Kinds;
with Why;                           use Why;
with Why.Atree.Accessors;           use Why.Atree.Accessors;
with Why.Atree.Builders;            use Why.Atree.Builders;
with Why.Atree.Modules;             use Why.Atree.Modules;
with Why.Conversions;               use Why.Conversions;
with Why.Gen.Arrays;                use Why.Gen.Arrays;
with Why.Gen.Binders;               use Why.Gen.Binders;
with Why.Gen.Decl;                  use Why.Gen.Decl;
with Why.Gen.Expr;                  use Why.Gen.Expr;
with Why.Gen.Hardcoded;             use Why.Gen.Hardcoded;
with Why.Gen.Init;                  use Why.Gen.Init;
with Why.Gen.Names;                 use Why.Gen.Names;
with Why.Gen.Pointers;              use Why.Gen.Pointers;
with Why.Gen.Progs;                 use Why.Gen.Progs;
with Why.Gen.Records;               use Why.Gen.Records;
with Why.Gen.Scalars;               use Why.Gen.Scalars;
with Why.Gen.Terms;                 use Why.Gen.Terms;
with Why.Inter;                     use Why.Inter;
with Why.Sinfo;                     use Why.Sinfo;
with Why.Types;                     use Why.Types;

package body Gnat2Why.Types is

   procedure Create_Initialization_Predicate
     (Th : Theory_UC; E : Type_Kind_Id; Predeclare : Boolean := False)
   with Pre => Has_Init_Wrapper (E);
   --  Create a function to state that objects of type E are initialized.
   --  If Predeclare is True, only emit a declaration and use a local name for
   --  the type associated to E.

   -------------------------------------
   -- Create_Initialization_Predicate --
   -------------------------------------

   procedure Create_Initialization_Predicate
     (Th : Theory_UC; E : Type_Kind_Id; Predeclare : Boolean := False)
   is
      Abstr_Ty : constant W_Type_Id := EW_Abstract (E, Relaxed_Init => True);
      Main_Ty  : constant W_Type_Id :=
        (if Predeclare
         then
           New_Named_Type
             (Name => To_Local (Get_Name (Abstr_Ty)), Relaxed_Init => True)
         else Abstr_Ty);
      Main_Arg : constant W_Identifier_Id :=
        New_Temp_Identifier (Typ => Main_Ty, Base_Name => "expr");
      --  Expression on which we want to assume the property

      Binders : constant Binder_Array :=
        Binder_Array'(1 => Binder_Type'(B_Name => Main_Arg, others => <>));

      Def : constant W_Pred_Id :=
        (if Predeclare
         then Why_Empty
         else
           +Compute_Is_Initialized
              (E                  => E,
               Name               => +Main_Arg,
               Params             => Logic_Params,
               Domain             => EW_Pred,
               Exclude_Components => Relaxed,
               Use_Pred           => False));

   begin
      --  ??? Here we should probably consider variable inputs occurring in
      --  potential predicates.

      Emit
        (Th,
         New_Function_Decl
           (Domain   => EW_Pred,
            Name     => To_Local (E_Symb (E, WNE_Is_Initialized_Pred)),
            Def      => +Def,
            Location => No_Location,
            Labels   => Symbol_Sets.Empty_Set,
            Binders  => Binders));
   end Create_Initialization_Predicate;

   ------------------------------
   -- Generate_Type_Completion --
   ------------------------------

   procedure Generate_Type_Completion (E : Type_Kind_Id) is

      --  Local subprograms

      procedure Complete_Initialization_Predicate
        (Th : Theory_UC; E : Type_Kind_Id)
      with Pre => Has_Init_Wrapper (E);
      --  Generate axioms to complete the definitions of Is_Initializes if it
      --  has been predeclared.

      procedure Create_Axioms_For_Scalar_Bounds
        (Th : Theory_UC; E : Type_Kind_Id);
      --  Create axioms defining the values of non-static scalar bounds

      procedure Create_Default_Init_Assumption
        (Th : Theory_UC; E : Type_Kind_Id);
      --  Create a function to express type E's default initial assumption

      procedure Create_Dynamic_Invariant
        (Th : Theory_UC; E : Type_Kind_Id; Module : W_Module_Id);
      --  Create a function to express type E's dynamic invariant. Module is
      --  the module in which dynamic invariants for access to incomplete
      --  types will be created if any.

      procedure Create_Type_Invariant (Th : Theory_UC; E : Type_Kind_Id)
      with Pre => Has_Invariants_In_SPARK (E);
      --  Create a function to express type E's invariant

      procedure Generate_Axioms_For_Equality (E : Type_Kind_Id);
      --  Generate axioms defining the equality functions __user_eq and
      --  __dispatch_eq on E.

      ---------------------------------------
      -- Complete_Initialization_Predicate --
      ---------------------------------------

      procedure Complete_Initialization_Predicate
        (Th : Theory_UC; E : Type_Kind_Id)
      is
         Main_Arg : constant W_Identifier_Id :=
           New_Temp_Identifier
             (Typ       => EW_Abstract (E, Relaxed_Init => True),
              Base_Name => "expr");
         --  Expression on which we want to assume the property

         Binders : constant Binder_Array :=
           Binder_Array'(1 => Binder_Type'(B_Name => Main_Arg, others => <>));

         Def : constant W_Pred_Id :=
           +Compute_Is_Initialized
              (E                  => E,
               Name               => +Main_Arg,
               Params             => Logic_Params,
               Domain             => EW_Pred,
               Exclude_Components => Relaxed,
               Use_Pred           => False);

      begin
         Emit
           (Th,
            New_Defining_Bool_Axiom
              (Name     => E_Symb (E, WNE_Is_Initialized_Pred),
               Fun_Name => To_String (WNE_Is_Initialized_Pred),
               Binders  => Binders,
               Dep_Kind => EW_Axdep_Pred,
               Def      => Def));
      end Complete_Initialization_Predicate;

      -------------------------------------
      -- Create_Axioms_For_Scalar_Bounds --
      -------------------------------------

      procedure Create_Axioms_For_Scalar_Bounds
        (Th : Theory_UC; E : Type_Kind_Id)
      is
         procedure Create_Axiom_For_Expr
           (Name : W_Identifier_Id; Bnd : Node_Id; Typ : W_Type_Id)
         with Pre => Nkind (Bnd) in N_Subexpr;
         --  Create a defining axiom for a logic function which can be used
         --  instead of E.

         ---------------------------
         -- Create_Axiom_For_Expr --
         ---------------------------

         procedure Create_Axiom_For_Expr
           (Name : W_Identifier_Id; Bnd : Node_Id; Typ : W_Type_Id)
         is
            Items : Item_Array := Get_Binders_From_Expression (Bnd);
            Def   : W_Term_Id;

         begin
            --  Use local names for variables

            Localize_Binders (Items, Only_Variables => False);

            --  Push the names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def :=
              +Transform_Expr
                 (Expr          => Bnd,
                  Expected_Type => Typ,
                  Domain        => EW_Term,
                  Params        => Logic_Params);

            Emit
              (Th,
               New_Defining_Axiom
                 (Name    => Name,
                  Def     => +Def,
                  Binders => To_Binder_Array (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end Create_Axiom_For_Expr;

         Rng  : constant Node_Id := Get_Range (E);
         Low  : constant Node_Id := Low_Bound (Rng);
         High : constant Node_Id := High_Bound (Rng);

         --  Start of processing for Create_Axioms_For_Scalar_Bounds

      begin
         if not Compile_Time_Known_Value (Low) then
            Create_Axiom_For_Expr
              (Name => E_Symb (E, WNE_Attr_First),
               Bnd  => Low,
               Typ  => Base_Why_Type (E));
         end if;
         if not Compile_Time_Known_Value (High) then
            Create_Axiom_For_Expr
              (Name => E_Symb (E, WNE_Attr_Last),
               Bnd  => High,
               Typ  => Base_Why_Type (E));
         end if;
      end Create_Axioms_For_Scalar_Bounds;

      ------------------------------------
      -- Create_Default_Init_Assumption --
      ------------------------------------

      procedure Create_Default_Init_Assumption
        (Th : Theory_UC; E : Type_Kind_Id)
      is
         Variables : Flow_Id_Sets.Set;

      begin
         --  Get the set of variables used in E's default initialization

         Variables_In_Default_Init (E, Variables);

         declare
            Items : constant Item_Array :=
              Get_Localized_Binders_From_Variables
                (Variables, Only_Variables => False);
            --  Use local names for variables

            Main_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier
                (Typ => Type_Of_Node (E), Base_Name => "expr");
            --  Expression on which we want to assume the property

            Slst_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier
                (Typ => EW_Bool_Type, Base_Name => "skip_top_level");
            --  Only assume initial condition for the components

            Def : W_Pred_Id;

         begin
            --  Push variable names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def :=
              Compute_Default_Init
                (Expr           => +Main_Arg,
                 Ty             => E,
                 Skip_Last_Cond => +Slst_Arg,
                 Params         => Logic_Params,
                 Use_Pred       => False);

            Emit
              (Th,
               New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => To_Local (E_Symb (E, WNE_Default_Init)),
                  Def      => +Def,
                  Labels   => Symbol_Sets.Empty_Set,
                  Location => No_Location,
                  Binders  =>
                    Binder_Array'
                      (1 => Binder_Type'(B_Name => Main_Arg, others => <>),
                       2 => Binder_Type'(B_Name => Slst_Arg, others => <>))
                    & To_Binder_Array (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end Create_Default_Init_Assumption;

      ------------------------------
      -- Create_Dynamic_Invariant --
      ------------------------------

      procedure Create_Dynamic_Invariant
        (Th : Theory_UC; E : Type_Kind_Id; Module : W_Module_Id)
      is
         procedure Create_Dynamic_Invariant
           (E            : Type_Kind_Id;
            Name         : W_Identifier_Id;
            Relaxed_Init : Boolean;
            For_Acc      : Boolean);
         --  Emit a declaration for the predicate symbol Name and define it to
         --  be the dynamic invariant for E. If For_Acc is true, split the
         --  definition into a declaration and a separate axiom to handle
         --  circularity.

         package Decl_Lists is new
           Ada.Containers.Doubly_Linked_Lists (W_Declaration_Id);

         Loc_Incompl_Acc : Ada_To_Why_Ident.Map;
         --  Map of all local symbols introduced for predicates of access to
         --  incomplete access types.

         Loc_Incompl_Acc_R : Ada_To_Why_Ident.Map;
         --  Same as above but for init wrappers

         Axioms : Decl_Lists.List;
         --  Axioms for predicates of access to incomplete access types

         ------------------------------
         -- Create_Dynamic_Invariant --
         ------------------------------

         procedure Create_Dynamic_Invariant
           (E            : Type_Kind_Id;
            Name         : W_Identifier_Id;
            Relaxed_Init : Boolean;
            For_Acc      : Boolean)
         is
            Variables : Flow_Id_Sets.Set;

         begin
            --  Get the set of variables used in E's dynamic property. Locally
            --  assumed predicates are not included.

            Variables_In_Dynamic_Invariant (E, Variables, Scop => Empty);

            declare
               Items : constant Item_Array :=
                 Get_Localized_Binders_From_Variables
                   (Variables, Only_Variables => False);
               --  Use local names for variables

               Init_Arg : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Typ => EW_Bool_Type, Base_Name => "is_init");
               --  Is the object known to be initialized

               Ovar_Arg : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Typ => EW_Bool_Type, Base_Name => "skip_constant");
               --  Do we need to assume the properties on constant parts

               Top_Arg : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Typ => EW_Bool_Type, Base_Name => "do_toplevel");
               --  Should we include the toplevel predicate

               Inv_Arg : constant W_Identifier_Id :=
                 New_Temp_Identifier
                   (Typ => EW_Bool_Type, Base_Name => "do_typ_inv");
               --  Should we include the non local type invariants

               Main_Ty : constant W_Type_Id :=
                 (if Relaxed_Init
                  then EW_Abstract (E, Relaxed_Init => True)
                  else Type_Of_Node (E));

               Main_Arg : constant W_Identifier_Id :=
                 New_Temp_Identifier (Typ => Main_Ty, Base_Name => "expr");
               --  Expression on which we want to assume the property

               Def               : W_Pred_Id;
               New_Incompl_Acc   : Ada_To_Why_Ident.Map;
               New_Incompl_Acc_R : Ada_To_Why_Ident.Map;

            begin
               --  Push variable names to Symbol_Table

               Ada_Ent_To_Why.Push_Scope (Symbol_Table);
               Push_Binders_To_Symbol_Table (Items);

               --  Compute the predicate for E. Do not include any locally
               --  assumed predicate, they will be added separately depending
               --  on the scope when the dynamic invariant is used. Do not
               --  handle validity flags. The dynamic invariant is expanded
               --  if one is provided.

               Compute_Dynamic_Invariant
                 (Expr              => +Main_Arg,
                  Ty                => E,
                  Initialized       => +Init_Arg,
                  Only_Var          => +Ovar_Arg,
                  Top_Predicate     => +Top_Arg,
                  All_Global_Inv    => +Inv_Arg,
                  Valid             => Why_Empty,
                  Inv_Scop          => Empty,
                  Inv_Subp          => Empty,
                  Params            => Logic_Params,
                  Use_Pred          => False,
                  New_Preds_Module  => Module,
                  T                 => Def,
                  Loc_Incompl_Acc   => Loc_Incompl_Acc,
                  New_Incompl_Acc   => New_Incompl_Acc,
                  Loc_Incompl_Acc_R => Loc_Incompl_Acc_R,
                  New_Incompl_Acc_R => New_Incompl_Acc_R,
                  Expand_Incompl    => False);

               --  Copy new predicate symbols to the map of local symbols

               for C in New_Incompl_Acc.Iterate loop
                  Loc_Incompl_Acc.Insert
                    (Ada_To_Why_Ident.Key (C), Ada_To_Why_Ident.Element (C));
               end loop;

               for C in New_Incompl_Acc_R.Iterate loop
                  Loc_Incompl_Acc_R.Insert
                    (Ada_To_Why_Ident.Key (C), Ada_To_Why_Ident.Element (C));
               end loop;

               --  Introduce function symbols (with no definitions) for
               --  new predicate symbols. Store their axioms in Axioms.

               for C in New_Incompl_Acc.Iterate loop
                  Create_Dynamic_Invariant
                    (E            => Ada_To_Why_Ident.Key (C),
                     Name         => Ada_To_Why_Ident.Element (C),
                     Relaxed_Init => False,
                     For_Acc      => True);
               end loop;

               for C in New_Incompl_Acc_R.Iterate loop
                  Create_Dynamic_Invariant
                    (E            => Ada_To_Why_Ident.Key (C),
                     Name         => Ada_To_Why_Ident.Element (C),
                     Relaxed_Init => True,
                     For_Acc      => True);
               end loop;

               declare
                  Binders : constant Binder_Array :=
                    Binder_Array'
                      (1 => Binder_Type'(B_Name => Main_Arg, others => <>),
                       2 => Binder_Type'(B_Name => Init_Arg, others => <>),
                       3 => Binder_Type'(B_Name => Ovar_Arg, others => <>),
                       4 => Binder_Type'(B_Name => Top_Arg, others => <>),
                       5 => Binder_Type'(B_Name => Inv_Arg, others => <>))
                    & To_Binder_Array (Items);
               begin

                  --  If we are defining a symbol for an access to an
                  --  incomplete type, split the predicate into a declaration
                  --  and a defining axiom to avoid circularity.

                  if For_Acc then
                     Emit
                       (Th,
                        New_Function_Decl
                          (Domain   => EW_Pred,
                           Name     => Name,
                           Labels   => Symbol_Sets.Empty_Set,
                           Binders  => Binders,
                           Location => No_Location));
                     Axioms.Append
                       (New_Defining_Bool_Axiom
                          (Fun_Name => Get (Get_Symb (Get_Name (Name))).all,
                           Name     => Name,
                           Binders  => Binders,
                           Def      => Def,
                           Dep_Kind => EW_Axdep_Pred));

                  --  Otherwise, define the symbol at declaration

                  else
                     Emit
                       (Th,
                        New_Function_Decl
                          (Domain   => EW_Pred,
                           Name     => Name,
                           Def      => +Def,
                           Location => No_Location,
                           Labels   => Symbol_Sets.Empty_Set,
                           Binders  => Binders));
                  end if;
               end;

               Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
            end;
         end Create_Dynamic_Invariant;

         --  Start of processing for Create_Dynamic_Invariant

      begin
         Create_Dynamic_Invariant
           (E            => E,
            Name         => To_Local (E_Symb (E, WNE_Dynamic_Invariant)),
            Relaxed_Init => False,
            For_Acc      => False);

         if Has_Init_Wrapper (E) then
            Create_Dynamic_Invariant
              (E            => E,
               Name         =>
                 To_Local
                   (E_Symb (E, WNE_Dynamic_Invariant, Relaxed_Init => True)),
               Relaxed_Init => True,
               For_Acc      => False);
         end if;

         --  Emit axioms for local predicate symbols

         for Ax of Axioms loop
            Emit (Th, Ax);
         end loop;
      end Create_Dynamic_Invariant;

      ---------------------------
      -- Create_Type_Invariant --
      ---------------------------

      procedure Create_Type_Invariant (Th : Theory_UC; E : Type_Kind_Id) is
         Variables : Flow_Id_Sets.Set;

      begin
         --  Get the set of variables used in E's predicate

         Variables_In_Type_Invariant (E, Variables);

         declare
            Items : constant Item_Array :=
              Get_Localized_Binders_From_Variables
                (Variables, Only_Variables => False);
            --  Use local names for variables

            Main_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => Type_Of_Node (E));
            --  Expression on which we want to assume the property
            Def      : W_Pred_Id;

         begin
            --  Push variable names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def :=
              Compute_Top_Level_Type_Invariant
                (Expr     => +Main_Arg,
                 Ty       => E,
                 Params   => Logic_Params,
                 Use_Pred => False);

            Emit
              (Th,
               Why.Gen.Binders.New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => To_Local (E_Symb (E, WNE_Type_Invariant)),
                  Def      => +Def,
                  Location => No_Location,
                  Labels   => Symbol_Sets.To_Set (NID (GP_Inline_Marker)),
                  Binders  =>
                    Binder_Array'
                      (1 => Binder_Type'(B_Name => Main_Arg, others => <>))
                    & To_Binder_Array (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end Create_Type_Invariant;

      -----------------------------------
      -- Generate_Axioms_For_Equality  --
      -----------------------------------

      procedure Generate_Axioms_For_Equality (E : Type_Kind_Id) is
         Eq                      : constant Entity_Id :=
           Get_User_Defined_Eq (Base_Type (E));
         Ty                      : constant W_Type_Id := EW_Abstract (E);
         Declares_Dispatching_Eq : constant Boolean :=
           Is_Tagged_Type (E)
           and then Root_Retysp (E) = E
           and then (if Present (Eq)
                     then not Is_Hidden_Dispatching_Operation (Eq));
         Var_A                   : constant W_Identifier_Id :=
           New_Identifier (Ada_Node => E, Name => "a", Typ => Ty);
         Var_B                   : constant W_Identifier_Id :=
           New_Identifier (Ada_Node => E, Name => "b", Typ => Ty);

         User_Th     : Theory_UC;
         Dispatch_Th : Theory_UC;

      begin
         if Declares_Dispatching_Eq then
            Dispatch_Th :=
              Open_Theory
                (WF_Context,
                 E_Module (E, Dispatch_Equality_Axiom),
                 Comment =>
                   "Module giving axioms for dispatching equality of record"
                   & " type """
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);
         end if;

         --  When there is a user-provided equality, generate an axiom to give
         --  the value of the user_eq symbol.

         if not Use_Predefined_Equality_For_Type (E)
           and then Entity_In_SPARK (Eq)
         then
            User_Th :=
              Open_Theory
                (WF_Context,
                 E_Module (E, User_Equality_Axiom),
                 Comment =>
                   "Module giving axioms for primitive equality of record"
                   & " type """
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);

            --  Go to the expected types without checking, checks are
            --  introduced separately.

            declare
               Binders : constant Item_Array :=
                 Compute_Subprogram_Parameters (Eq, EW_Term);
               pragma Assert (Binders'Length = 2);
               Arg_A   : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => +Var_A,
                    To     => Get_Why_Type_From_Item (Binders (1)));
               Arg_B   : constant W_Expr_Id :=
                 Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr   => +Var_B,
                    To     => Get_Why_Type_From_Item (Binders (2)));
               Def     : constant W_Expr_Id :=
                 (if Is_Hardcoded_Entity (Eq)

                    --  If the equality is hardcoded, we define user_eq as its
                    --  hardcoded definition.

                    then
                    Transform_Hardcoded_Function_Call
                      (Subp     => Eq,
                       Args     => (Arg_A, Arg_B),
                       Domain   => EW_Term,
                       Ada_Node => Eq)
                  else
                    New_Function_Call
                      (Ada_Node => Eq,
                       Domain   => EW_Term,
                       Name     =>
                         To_Why_Id
                           (E => Eq, Domain => EW_Term, Typ => EW_Bool_Type),
                       Subp     => Eq,
                       Args     => (1 => Arg_A, 2 => Arg_B),
                       Check    => False,
                       Typ      => EW_Bool_Type));
            begin
               Emit
                 (User_Th,
                  New_Defining_Axiom
                    (Ada_Node => E,
                     Binders  =>
                       (1 => Binder_Type'(B_Name => Var_A, others => <>),
                        2 => Binder_Type'(B_Name => Var_B, others => <>)),
                     Name     => E_Symb (E, WNE_User_Eq),
                     Def      => +Def));

               Close_Theory (User_Th, Kind => Definition_Theory);
               Record_Extra_Dependency
                 (Defining_Module => E_Module (E, User_Equality),
                  Axiom_Module    => User_Th.Module);

               --  If E is the root of a tagged hierarchy, also generate a
               --  definition for the dispatching equality symbol.

               if Declares_Dispatching_Eq then

                  --  We don't handle hardcoded dispatching equality yet

                  if Is_Hardcoded_Entity (Eq) then
                     raise Program_Error;
                  end if;

                  declare
                     Tag_Id : constant W_Identifier_Id :=
                       New_Identifier
                         (Name => To_String (WNE_Attr_Tag),
                          Typ  => EW_Int_Type);
                  begin
                     Emit
                       (Dispatch_Th,
                        New_Defining_Axiom
                          (Ada_Node => E,
                           Binders  =>
                             (1 =>
                                Binder_Type'(B_Name => Tag_Id, others => <>),
                              2 => Binder_Type'(B_Name => Var_A, others => <>),
                              3 =>
                                Binder_Type'(B_Name => Var_B, others => <>)),
                           Name     => E_Symb (E, WNE_Dispatch_Eq),
                           Def      =>
                             +New_Function_Call
                                (Ada_Node => Eq,
                                 Domain   => EW_Term,
                                 Selector => Dispatch,
                                 Name     =>
                                   To_Why_Id
                                     (E        => Eq,
                                      Domain   => EW_Term,
                                      Typ      => EW_Bool_Type,
                                      Selector => Dispatch),
                                 Subp     => Eq,
                                 Args     =>
                                   (1 => +Tag_Id, 2 => Arg_A, 3 => Arg_B),
                                 Check    => False,
                                 Typ      => EW_Bool_Type)));
                  end;
               end if;
            end;

         --  If E is a tagged type, emit a compatibility axiom for its
         --  dispatching equality. No need for a compatibility axiom if the
         --  equality on the root type was redefined, because in this case we
         --  already have a defining axiom for the dispatching equality.

         elsif Declares_Dispatching_Eq and then not Is_Concurrent_Type (E) then
            declare
               Descendants : Node_Sets.Set := Get_Descendant_Set (E);
               Dispatch_Eq : constant W_Identifier_Id :=
                 E_Symb (E, WNE_Dispatch_Eq);
               D_Tag       : W_Identifier_Id;

            begin
               Descendants.Insert (E);

               --  For each descendant D of E, generate:
               --
               --  axiom <D>__compat_axiom:
               --    forall a :e, b : e [__dispatch_eq <D>.__tag a b].
               --      (attr__tag a = <D>.__tag /\ attr__tag b = <D>.__tag) ->
               --         __dispatch_eq <D>.__tag a b =
               --           <D>.bool_eq (<D>.of_base a) (<D>.of_base b)
               --
               --  if D uses the predefined equality, and
               --
               --  axiom <D>__compat_axiom:
               --    forall a :e, b : e [__dispatch_eq <D>.__tag a b].
               --      (attr__tag a = <D>.__tag /\ attr__tag b = <D>.__tag) ->
               --         __dispatch_eq <D>.__tag a b =
               --            <D>.user_eq (<D>.of_base a) (<D>.of_base b)
               --
               --  otherwise.

               for D of Descendants loop
                  D_Tag := E_Symb (D, WNE_Tag);
                  Emit
                    (Dispatch_Th,
                     New_Guarded_Axiom
                       (Binders  =>
                          (1 => Binder_Type'(B_Name => Var_A, others => <>),
                           2 => Binder_Type'(B_Name => Var_B, others => <>)),
                        Triggers =>
                          New_Triggers
                            (Triggers =>
                               (1 =>
                                  New_Trigger
                                    (Terms =>
                                       (1 =>
                                          +W_Term_Id'
                                            (New_Call
                                               (Name => Dispatch_Eq,
                                                Args =>
                                                  (+D_Tag, +Var_A, +Var_B),
                                                Typ  => EW_Bool_Type)))))),
                        Name     => NID (Full_Name (D) & "__" & Compat_Axiom),
                        Pre      =>
                          New_And_Pred
                            (Left  =>
                               New_Comparison
                                 (Symbol => Why_Eq,
                                  Left   =>
                                    +New_Tag_Access
                                       (Domain => EW_Term,
                                        Name   => +Var_A,
                                        Ty     => E),
                                  Right  => +D_Tag),
                             Right =>
                               New_Comparison
                                 (Symbol => Why_Eq,
                                  Left   =>
                                    +New_Tag_Access
                                       (Domain => EW_Term,
                                        Name   => +Var_B,
                                        Ty     => E),
                                  Right  => +D_Tag)),
                        Def      =>
                          New_Comparison
                            (Symbol => Why_Eq,
                             Left   =>
                               New_Call
                                 (Name => Dispatch_Eq,
                                  Args => (+D_Tag, +Var_A, +Var_B),
                                  Typ  => EW_Bool_Type),
                             Right  =>
                               +New_Ada_Equality
                                  (Typ    => D,
                                   Domain => EW_Term,
                                   Left   =>
                                     +W_Term_Id'
                                       (New_Call
                                          (Name => E_Symb (D, WNE_Of_Base),
                                           Args => (1 => +Var_A),
                                           Typ  => EW_Abstract (D))),
                                   Right  =>
                                     +W_Term_Id'
                                       (New_Call
                                          (Name => E_Symb (D, WNE_Of_Base),
                                           Args => (1 => +Var_B),
                                           Typ  => EW_Abstract (D)))))));
               end loop;
            end;
         end if;

         if Declares_Dispatching_Eq then
            Close_Theory (Dispatch_Th, Kind => Definition_Theory);
            Record_Extra_Dependency
              (Defining_Module => E_Module (E, Dispatch_Equality),
               Axiom_Module    => Dispatch_Th.Module);
         end if;
      end Generate_Axioms_For_Equality;

      Th : Theory_UC;

      --  Start of processing for Generate_Type_Completion

   begin
      Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Axiom),
           Comment =>
             "Module giving axioms for type "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      if Is_Access_Subprogram_Type (E) then

         --  Generate program function for E

         Complete_Access_To_Subprogram_Type (Th, E);

      elsif Is_Tagged_Type (E) then

         --  If E is a root of a tagged hierarchy, generate axioms for the
         --  compatibility of the concrete tags of its visible descendants.

         if E = Root_Retysp (E) and then not Is_Concurrent_Type (E) then
            Create_Compatible_Tags_Theory (E);
         end if;

         Complete_Tagged_Record_Type (Th, E);
      end if;

      --  Generate a predicate for E's dynamic property. For provability, it is
      --  inlined by Why3.
      --  We do not generate the dynamic property for Itypes as they may
      --  depend on locally defined constants such as 'Old.

      if not Is_Itype (E)
        and then not Is_Standard_Boolean_Type (E)
        and then E /= Universal_Fixed
      then
         Create_Dynamic_Invariant (Th, E, E_Module (E, Axiom));
      end if;

      --  If E is a scalar type with dynamic bounds, we give axioms for the
      --  values of its bounds.

      if not Is_Itype (E) and then Is_Scalar_Type (E) then
         Create_Axioms_For_Scalar_Bounds (Th, E);
      end if;

      if Has_Init_Wrapper (E)
        and then not Is_Scalar_Type (E)
        and then not Is_Itype (E)
      then
         if Has_Predeclared_Init_Predicate (E) then
            Complete_Initialization_Predicate (Th, E);
         else
            Create_Initialization_Predicate (Th, E);
         end if;
      end if;

      Close_Theory (Th, Kind => Axiom_Theory, Defined_Entity => E);

      --  Generate a predicate for E's default initialization.
      --  We do not generate default initialization for unconstrained types.

      if not Is_Itype (E) and then Can_Be_Default_Initialized (E) then
         Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Default_Initialialization),
              Comment =>
                "Module giving a predicate for the default initial assumption"
                & " of type """
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
         Create_Default_Init_Assumption (Th, E);
         Close_Theory (Th, Kind => Definition_Theory);
      end if;

      if Has_Invariants_In_SPARK (E) then
         Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Invariant),
              Comment =>
                "Module giving a predicate for the type invariant of"
                & " type """
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);
         Create_Type_Invariant (Th, E);
         Close_Theory (Th, Kind => Definition_Theory);
      end if;

      --  For types which need reclamation, generate a move tree theory.

      if Contains_Allocated_Parts (E) then
         Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Move_Tree),
              Comment =>
                "Module for move trees for objects of type "
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);

         if Is_Record_Type_In_Why (E) then
            Create_Move_Tree_Theory_For_Record (Th, E);
         elsif Has_Array_Type (E) then
            Create_Move_Tree_Theory_For_Array (Th, E);

         --  No need to generate move tree theories for anonymous access types
         --  as objects of these types do not need to be reclaimed themselves.
         --  The tree of their designated type will be used instead if it
         --  contains allocated parts.

         elsif not Is_Anonymous_Access_Type (E) then
            pragma Assert (Has_Access_Type (E));
            Create_Move_Tree_Theory_For_Pointer (Th, E);
         end if;

         --  After generating the move tree theory of an incomplete
         --  type, complete its early declarations.

         if Has_Incomplete_Access (E) then
            Complete_Move_Tree_For_Incomplete_Access (Th, E);
         end if;

         --  Create a __moved_tree function returning a moved tree. Generate:
         --
         --    val moved_tree (obj : ty) : move_tree
         --      ensures { is_moved_or_reclaimed result obj }

         if not Is_Anonymous_Access_Type (E)
           and then (not Is_Record_Type_In_Why (E)
                     or else not Record_Type_Is_Clone (E))
         then
            declare
               Typ           : constant W_Type_Id :=
                 (if Has_Init_Wrapper (E)
                  then EW_Init_Wrapper (Type_Of_Node (E))
                  else Type_Of_Node (E));
               Obj_Binder    : constant Binder_Type :=
                 (B_Name => New_Identifier (Name => "obj", Typ => Typ),
                  others => <>);
               Moved_Tree_Id : constant W_Identifier_Id :=
                 New_Identifier
                   (Domain => EW_Term, --  factor out
                    Symb   => NID (To_String (WNE_Moved_Tree)),
                    Typ    => New_Named_Type (To_Name (WNE_Move_Tree)));

            begin
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => Moved_Tree_Id,
                     Binders     => Binder_Array'(1 => Obj_Binder),
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Get_Typ (Moved_Tree_Id),
                     Post        =>
                       New_Call
                         (Name =>
                            To_Local (E_Symb (E, WNE_Is_Moved_Or_Reclaimed)),
                          Args =>
                            (1 => +New_Result_Ident (Get_Typ (Moved_Tree_Id)),
                             2 => +Obj_Binder.B_Name))));
            end;
         end if;

         Close_Theory (Th, Kind => Definition_Theory);

         if Has_Incomplete_Access (E) then
            Record_Extra_Dependency
              (Defining_Module => E_Module (E, Incomp_Move_Tree),
               Axiom_Module    => Th.Module);
         end if;
      end if;

      if (Is_Tagged_Type (E) and then E = Root_Retysp (E))
        or else not Use_Predefined_Equality_For_Type (E)
      then
         Generate_Axioms_For_Equality (E);
      end if;
   end Generate_Type_Completion;

   ---------------------------
   -- Generate_VCs_For_Type --
   ---------------------------

   procedure Generate_VCs_For_Type (E : Type_Kind_Id) is
      Priv_View       : constant Opt_Type_Kind_Id :=
        Find_View_For_Default_Checks (E);
      Check_Default   : constant Boolean := Present (Priv_View);
      Check_Subp      : constant Boolean :=
        Is_Access_Subprogram_Type (E) and then No (Parent_Retysp (E));
      Check_Iter      : constant Boolean := Declares_Iterable_Aspect (E);
      Check_Eq        : constant Boolean :=
        Is_Base_Type (E) and then not Use_Predefined_Equality_For_Type (E);
      Check_Aggr      : constant Boolean :=
        Needs_Check_For_Aggregate_Annotation (E);
      Check_Ownership : constant Boolean := Needs_Ownership_Check (E);
      Need_Check      : constant Boolean :=
        Check_Default
        or else Check_Iter
        or else Check_Subp
        or else Check_Eq
        or else Check_Aggr
        or else Check_Ownership;
      Name            : constant String := Full_Name (E);
      S_Ty            : constant Entity_Id :=
        (if Present (First_Subtype (E))
           and then Entity_In_SPARK (First_Subtype (E))
         then First_Subtype (E)
         else E);
      --  Use the first subtype if any, as it can be more
      --  constrained than the base type introduced by the
      --  compiler.
      Params          : constant Transformation_Params := Body_Params;
      Why_Body        : W_Prog_Id := +Void;
      Th              : Theory_UC;
   begin
      if not Need_Check then
         return;
      end if;

      Th :=
        Open_Theory
          (WF_Main,
           New_Module (Name => Name & "__default_checks", File => No_Symbol),
           Comment =>
             "Module for checking DIC of default value and"
             & " absence of runtime errors in the private part of "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      Register_VC_Entity (E);

      if Check_Default then

         --  For private and private extension declaration,
         --  check the default expression of newly declared fields.

         Why_Body :=
           Sequence
             (Why_Body,
              New_Ignore
                (Prog =>
                   Compute_Default_Check
                     (Ada_Node         => Priv_View,
                      Ty               => Retysp (E),
                      Params           => Params,
                      At_Declaration   => True,
                      Include_Subtypes => True)));

         --  If the type has a DIC and this DIC should be checked at
         --  declaration, check that there can be no runtime error
         --  in the DIC and that default values of the type and all
         --  its subtypes respect the DIC.

         if Has_DIC (Priv_View) and then Needs_DIC_Check_At_Decl (Priv_View)
         then
            Why_Body :=
              Sequence
                (Why_Body,
                 Check_Type_With_DIC (Params => Params, Ty => Priv_View));
         end if;

      end if;

      --  If the type has an iterable aspect, insert checks
      --  that a quantified expression on the elements
      --  of the type will always execute correctly
      --  without run-time errors.

      if Check_Iter then
         Why_Body :=
           Sequence
             (New_Ignore (Ada_Node => E, Prog => Why_Body),
              Check_Type_With_Iterable (Params => Params, Ty => E));
      end if;

      --  If E has a primitive equality which will be used for membersip tests
      --  and equality on composite types, check that it can be called safely
      --  in any context.
      --
      --  Generate:
      --
      --    let x = any <E> { <dynamic_property of E> } in
      --    let y = any <E> { <dynamic_property of E> } in
      --      ignore (eq x y)

      if Check_Eq then
         declare
            Eq : constant Entity_Id := Get_User_Defined_Eq (Base_Type (E));
         begin
            --  To limit the number of checks on hardcoded entities, assume
            --  that hardcoded equality functions are correct here.

            if Entity_In_SPARK (Eq) and then not Is_Hardcoded_Entity (Eq) then
               Continuation_Stack.Append
                 (Continuation_Type'
                    (E,
                     To_Unbounded_String
                       ("primitive equality should be callable in any context"
                        & " for type")));
               declare
                  Binders : constant Item_Array :=
                    Compute_Subprogram_Parameters (Eq, EW_Term);
                  pragma Assert (Binders'Length = 2);

                  W_Ty   : constant W_Type_Id := Type_Of_Node (S_Ty);
                  Result : constant W_Identifier_Id := New_Result_Ident (W_Ty);
                  W_Post : constant W_Pred_Id :=
                    Compute_Dynamic_Inv_And_Initialization
                      (Expr        => +Result,
                       Ty          => Retysp (E),
                       Initialized => True_Term,
                       Only_Var    => False_Term,
                       Params      => Params);
                  X_Id   : constant W_Identifier_Id :=
                    New_Temp_Identifier (Typ => W_Ty);
                  Y_Id   : constant W_Identifier_Id :=
                    New_Temp_Identifier (Typ => W_Ty);
                  Arg_X  : constant W_Expr_Id :=
                    Insert_Checked_Conversion
                      (Ada_Node => First_Formal (Eq),
                       Domain   => EW_Prog,
                       Expr     => +X_Id,
                       To       => Get_Why_Type_From_Item (Binders (1)));
                  Arg_Y  : constant W_Expr_Id :=
                    Insert_Checked_Conversion
                      (Ada_Node => Next_Formal (First_Formal (Eq)),
                       Domain   => EW_Prog,
                       Expr     => +Y_Id,
                       To       => Get_Why_Type_From_Item (Binders (2)));
                  Pre_N  : constant Node_Lists.List :=
                    Find_Contracts (Eq, Pragma_Precondition);
                  Def    : constant W_Expr_Id :=
                    New_Function_Call
                      (Ada_Node =>
                         (if Pre_N.Is_Empty then Eq else Pre_N.First_Element),
                       Domain   => EW_Prog,
                       Name     =>
                         To_Why_Id
                           (E => Eq, Domain => EW_Prog, Typ => EW_Bool_Type),
                       Subp     => Eq,
                       Args     => (1 => Arg_X, 2 => Arg_Y),
                       Check    => Why_Subp_Has_Precondition (Eq),
                       Typ      => EW_Bool_Type);
                  Check  : W_Prog_Id := New_Ignore (Prog => +Def);
               begin
                  Check :=
                    New_Typed_Binding
                      (Name    => X_Id,
                       Def     =>
                         New_Any_Expr
                           (Ada_Node    => E,
                            Post        => W_Post,
                            Labels      => Symbol_Sets.Empty_Set,
                            Return_Type => W_Ty),
                       Context =>
                         New_Typed_Binding
                           (Name    => Y_Id,
                            Def     =>
                              New_Any_Expr
                                (Ada_Node    => E,
                                 Post        => W_Post,
                                 Labels      => Symbol_Sets.Empty_Set,
                                 Return_Type => W_Ty),
                            Context => Check));
                  Why_Body := Sequence (Why_Body, New_Ignore (Prog => Check));
               end;
               Continuation_Stack.Delete_Last;
            end if;
         end;
      end if;

      --  Generate checks to make sure that the translation used for container
      --  aggregates is correct. This is done by checking the initialization
      --  and the preservation of the associated invariants.

      if Check_Aggr then
         Why_Body :=
           Sequence
             (Why_Body,
              New_Ignore (Prog => Generate_VCs_For_Aggregate_Annotation (E)));
      end if;

      --  Generate checks for the reclamation function of E. If an object of
      --  type E is considered to be reclaimed as per its ownership annotation,
      --  it should be reclaimed (or moved but this cannot occur) for its full
      --  view. Generate:
      --
      --  let value = any <E> { <dynamic_property of E> } in
      --  assert { is_reclaimed value -> is_moved value }

      if Check_Ownership then
         declare
            W_Ty               : constant W_Type_Id := Type_Of_Node (S_Ty);
            W_Post             : constant W_Pred_Id :=
              Compute_Dynamic_Inv_And_Initialization
                (Expr        => +New_Result_Ident (W_Ty),
                 Ty          => Retysp (E),
                 Initialized => True_Term,
                 Only_Var    => False_Term,
                 Params      => Params);
            Value_Id           : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => W_Ty, Base_Name => "reclaimed");
            Tree_Id            : constant W_Identifier_Id :=
              New_Temp_Identifier
                (Typ => Get_Move_Tree_Type (S_Ty), Base_Name => "move_tree");
            Check              : W_Prog_Id;
            Reclamation_Entity : Entity_Id;
            Kind               : Reclamation_Kind;
         begin
            Get_Reclamation_Entity
              (Retysp (E), Reclamation_Entity, Kind, For_Check => True);
            Check :=
              New_Located_Assert
                (Ada_Node => Reclamation_Entity,
                 Pred     =>
                   New_Conditional
                     (Condition =>
                        Compute_Is_Reclaimed_For_Ownership
                          (Expr => +Value_Id, Ty => E, For_Check => True),
                      Then_Part =>
                        Compute_Is_Moved_Or_Reclaimed
                          (Expr => +Value_Id, Tree => +Tree_Id, Ty => S_Ty)),
                 Reason   => VC_Reclamation_Check,
                 Kind     => EW_Assert);
            Check :=
              New_Typed_Binding
                (Name    => Value_Id,
                 Def     =>
                   New_Any_Expr
                     (Ada_Node    => E,
                      Post        => W_Post,
                      Labels      => Symbol_Sets.Empty_Set,
                      Return_Type => W_Ty),
                 Context => Check);
            Check :=
              New_Typed_Binding
                (Name    => Tree_Id,
                 Def     =>
                   New_Any_Expr
                     (Ada_Node    => E,
                      Labels      => Symbol_Sets.Empty_Set,
                      Return_Type => Get_Typ (Tree_Id)),
                 Context => Check);
            Why_Body := Sequence (Why_Body, New_Ignore (Prog => Check));
         end;
      end if;

      if Why_Body /= +Void then
         --  Assume values of constants

         Assume_Value_Of_Constants (Why_Body, E, Params);

         Emit
           (Th,
            Why.Gen.Binders.New_Function_Decl
              (Domain   => EW_Prog,
               Name     => Def_Name,
               Binders  => (1 => Unit_Param),
               Location => No_Location,
               Labels   => Symbol_Sets.Empty_Set,
               Def      => +Why_Body));
      end if;

      --  Introduce checks for access-to-subprogram types. This can include
      --  checks for preconditions, and feasibility checks for
      --  access-to-functions.

      if Check_Subp then
         declare
            Name    : constant W_Identifier_Id :=
              New_Identifier (Symb => NID ("subp__def"), Domain => EW_Term);
            Profile : constant Entity_Id := Directly_Designated_Type (E);
         begin
            Generate_VCs_For_Subprogram (Profile, Th, Name);
         end;
      end if;

      Close_Theory (Th, Kind => VC_Generation_Theory, Defined_Entity => E);

   end Generate_VCs_For_Type;

   -----------------------
   -- Ident_Of_Ada_Type --
   -----------------------

   function Ident_Of_Ada_Type (E : Type_Kind_Id) return W_Name_Id is
   begin
      return
        (if Is_Standard_Boolean_Type (E)
         then Get_Name (EW_Bool_Type)
         else To_Why_Type (E));
   end Ident_Of_Ada_Type;

   --------------------
   -- Translate_Type --
   --------------------

   procedure Translate_Type (E : Type_Kind_Id) is

      procedure Create_Additional_Equality_Theories (E : Entity_Id)
      with
        Pre =>
          (Is_Tagged_Type (E) and then E = Root_Retysp (E))
          or else not Use_Predefined_Equality_For_Type (E);
      --  Create a module for the primitive equality __user_eq on values of
      --  type E and another module for the dispatching equality on E if it is
      --  the root of a tagged hierarchy.

      procedure Generate_Ref_Type_And_Havoc_Fun
        (Th : Theory_UC; E : Entity_Id; Relaxed_Init : Boolean);
      --  Generate a record type containing only one mutable field of
      --  type t. This is used to store mutable variables of type t.
      --  Also generate a havoc function for this type.

      procedure Translate_Underlying_Type (Th : Theory_UC; E : Entity_Id);
      --  Translate a non-private type entity E

      -----------------------------------------
      -- Create_Additional_Equality_Theories --
      -----------------------------------------

      procedure Create_Additional_Equality_Theories (E : Entity_Id) is
         W_Type  : constant W_Type_Id := EW_Abstract (E);
         A_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "a", Typ => W_Type);
         B_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => W_Type);
         Binders : constant Binder_Array :=
           (1 => (B_Name => A_Ident, others => <>),
            2 => (B_Name => B_Ident, others => <>));
         Th      : Theory_UC;

      begin
         --  Declare place-holder for primitive equality function

         if not Use_Predefined_Equality_For_Type (E) then
            Th :=
              Open_Theory
                (WF_Context,
                 E_Module (E, User_Equality),
                 Comment =>
                   "Module for primitive equality of record type "
                   & """"
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_User_Eq)),
                  Return_Type => EW_Bool_Type,
                  Binders     => Binders,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));

            Close_Theory (Th, Kind => Definition_Theory);
         end if;

         --  Declare the dispatching equality function in root tagged types

         if Is_Tagged_Type (E) and then E = Root_Retysp (E) then
            Th :=
              Open_Theory
                (WF_Context,
                 E_Module (E, Dispatch_Equality),
                 Comment =>
                   "Module for dispatching equality of record type "
                   & """"
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Dispatch_Eq)),
                  Return_Type => EW_Bool_Type,
                  Binders     =>
                    Binder_Type'
                      (B_Name =>
                         New_Identifier
                           (Name => To_String (WNE_Attr_Tag),
                            Typ  => EW_Int_Type),
                       others => <>)
                    & Binders,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));

            Close_Theory (Th, Kind => Definition_Theory);
         end if;
      end Create_Additional_Equality_Theories;

      -------------------------------------
      -- Generate_Ref_Type_And_Havoc_Fun --
      -------------------------------------

      procedure Generate_Ref_Type_And_Havoc_Fun
        (Th : Theory_UC; E : Entity_Id; Relaxed_Init : Boolean) is
      begin
         --  We do not generate these declarations for array or record types
         --  which are clones of existing types with the same name and
         --  statically constrained array type as no new type is declared for
         --  them.
         --  Classwide types are a special case as they are clones of their
         --  specific types but do not have the same short name.

         if (not (Has_Record_Type (E)
                  or else Has_Incomplete_Or_Private_Type (E))
             or else not Record_Type_Is_Clone (Retysp (E))
             or else Short_Name (Retysp (E))
                     /= Short_Name (Record_Type_Cloned_Subtype (Retysp (E))))
           and then not Is_Class_Wide_Type (Retysp (E))
           and then (not Has_Array_Type (E)
                     or else not Is_Static_Array_Type (Retysp (E)))
           and then (not Has_Array_Type (E)
                     or else not Array_Type_Is_Clone (Retysp (E))
                     or else Short_Name (Retysp (E))
                             /= Short_Name
                                  (Array_Type_Cloned_Subtype (Retysp (E))))
         then
            Emit_Ref_Type_Definition
              (Th,
               To_Why_Type
                 (Retysp (E), Local => True, Relaxed_Init => Relaxed_Init));
            Emit
              (Th,
               New_Havoc_Declaration
                 (Name =>
                    To_Why_Type
                      (Retysp (E),
                       Local        => True,
                       Relaxed_Init => Relaxed_Init)));
         end if;
      end Generate_Ref_Type_And_Havoc_Fun;

      -------------------------------
      -- Translate_Underlying_Type --
      -------------------------------

      procedure Translate_Underlying_Type (Th : Theory_UC; E : Entity_Id) is
      begin
         case Ekind (E) is
            when Scalar_Kind =>
               Declare_Scalar_Type (Th, E);

            when Array_Kind =>
               Declare_Ada_Array (Th, E);

            when E_Record_Type | E_Record_Subtype | Concurrent_Kind =>
               Declare_Ada_Record (Th, E);

            when Class_Wide_Kind =>
               Add_Use_For_Entity
                 (Th,
                  Specific_Tagged (E),
                  EW_Export,
                  With_Completion => False);

            when Incomplete_Or_Private_Kind =>
               pragma Assert (Full_View_Not_In_SPARK (E));
               Declare_Ada_Record (Th, E);

            when Access_Kind =>
               if Is_Access_Subprogram_Type (E) then
                  Declare_Access_To_Subprogram_Type (Th, E);
               else
                  Declare_Ada_Pointer (Th, E);
               end if;

            when others =>
               Ada.Text_IO.Put_Line
                 ("[Translate_Underlying_Type] ekind ="
                  & Entity_Kind'Image (Ekind (E)));
               raise Not_Implemented;
         end case;
      end Translate_Underlying_Type;

      Th : Theory_UC;

      --  Start of processing for Translate_Type

   begin
      if Is_Standard_Boolean_Type (E) or else E = Universal_Fixed then
         return;

      else
         if Has_Array_Type (E) then
            Create_Rep_Array_Theory_If_Needed (E);
         elsif Retysp_Kind (E)
               in Incomplete_Or_Private_Kind
                | E_Record_Type
                | E_Record_Subtype
                | Concurrent_Kind
         then
            Create_Rep_Record_Theory_If_Needed (Retysp (E));
         elsif Is_Access_Subprogram_Type (Retysp (E)) then

            --  Declare __call function for the designated profile if
            --  needed.

            Create_Theory_For_Profile_If_Needed (Retysp (E));
         elsif Has_Access_Type (E) then
            Create_Rep_Pointer_Theory_If_Needed (Retysp (E));
         end if;

         Th :=
           Open_Theory
             (WF_Context,
              E_Module (E),
              Comment =>
                "Module for axiomatizing type "
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);

         Translate_Underlying_Type (Th, Retysp (E));

         --  We declare a default value for all types, in principle.
         --  Cloned subtypes are a special case, they do not need such a
         --  definition.

         if (Has_Record_Type (E) or else Has_Incomplete_Or_Private_Type (E))
           and then not Record_Type_Is_Clone (Retysp (E))
         then
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
         end if;

         Generate_Ref_Type_And_Havoc_Fun (Th, E, Relaxed_Init => False);

         --  If E is the full view of a private type, use its partial view as
         --  the filtering entity, as it is the entity used everywhere in AST.

         Close_Theory
           (Th,
            Kind           => Definition_Theory,
            Defined_Entity =>
              (if Is_Full_View (E) then Partial_View (E) else E));

         --  For scalar types that are not modeled using their base types
         --  declare a Module where the functions to_rep/of_rep are defined.
         --  This let us separate the different axioms (inversion/range/coerce)
         --  to try and minimalize quantified axioms in the VCs' context.

         if Is_Scalar_Type (E) and then not Type_Is_Modeled_As_Base (E) then
            Th :=
              Open_Theory
                (WF_Context,
                 E_Module (E, Type_Representative),
                 Comment =>
                   "Module defining to_rep/of_rep for type "
                   & """"
                   & Get_Name_String (Chars (E))
                   & """"
                   & (if SPARK_Atree.Sloc (E) > 0
                      then " defined at " & Build_Location_String (Sloc (E))
                      else "")
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);

            Define_Scalar_Rep_Proj (Th, E);

            Close_Theory (Th, Kind => Standalone_Theory);
         end if;

         --  Declare to_string and of_string functions used for 'Image and
         --  'Value attributes.

         if E = Standard_String then
            Th :=
              Open_Theory
                (WF_Context,
                 String_Image_Module,
                 Comment =>
                   "Module defining to_string/of_string functions"
                   & ", created in "
                   & GNAT.Source_Info.Enclosing_Entity);

            Declare_Additional_Symbols_For_String (Th);

            Close_Theory (Th, Kind => Standalone_Theory);
         end if;
      end if;

      --  If the type may be used for expressions with relaxed initialization,
      --  declare a type with init flags for it.

      if Has_Init_Wrapper (E) then
         Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Init_Wrapper),
              Comment =>
                "Module defining a wrapper to verify initialization for type "
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if SPARK_Atree.Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);

         Declare_Init_Wrapper (Th, E);

         --  We declare a reference type and an havoc function for the init
         --  wrapper as well as move functions. For record types, the init
         --  wrapper module might have been cloned if E has a parent with the
         --  same fields. In this case, we should not regenerate the move
         --  predicates. It is still necessary to regenerate the reference type
         --  and havoc function if the types have different names as those
         --  are named after the type.

         if not Is_Record_Type_In_Why (Retysp (E))
           or else Oldest_Parent_With_Same_Fields (Retysp (E)) = Retysp (E)
         then
            Generate_Ref_Type_And_Havoc_Fun (Th, E, Relaxed_Init => True);
         elsif Short_Name (Retysp (E))
           /= Short_Name (Oldest_Parent_With_Same_Fields (Retysp (E)))
         then
            Generate_Ref_Type_And_Havoc_Fun (Th, E, Relaxed_Init => True);
         end if;

         if Has_Predeclared_Init_Predicate (E) then
            Create_Initialization_Predicate (Th, E, Predeclare => True);
         end if;

         Close_Theory (Th, Kind => Definition_Theory);
      end if;

      --  After translating the full view of an incomplete type, complete the
      --  representation of the corresponding access type representative
      --  theory.

      if Has_Incomplete_Access (E) then
         Create_Rep_Pointer_Theory_If_Needed (Get_Incomplete_Access (E));
         Declare_Rep_Pointer_Compl_If_Needed
           (Repr_Pointer_Type (Get_Incomplete_Access (E)));

         --  Declare an incomplete version of the move tree type and of the
         --  is_moved_or_reclaimed predicate.

         if Contains_Allocated_Parts (E) then
            Create_Move_Tree_For_Incomplete_Access (E);
         end if;
      end if;

      --  For record types, potentially declare theories for the __user_eq
      --  (primitive equality) and __dispatch_eq (dispatching equality)
      --  symbols.

      if (Is_Tagged_Type (E) and then E = Root_Retysp (E))
        or else not Use_Predefined_Equality_For_Type (E)
      then
         Create_Additional_Equality_Theories (E);
      end if;

      --  Create a theory for validity trees of composite objects of type E if
      --  necessary.

      if Type_Might_Be_Invalid (E)
        and then not Has_Scalar_Type (E)
        and then E = Base_Retysp (E)
      then
         Th :=
           Open_Theory
             (WF_Context,
              E_Module (E, Validity_Tree),
              Comment =>
                "Module for validity trees for objects of type "
                & """"
                & Get_Name_String (Chars (E))
                & """"
                & (if Sloc (E) > 0
                   then " defined at " & Build_Location_String (Sloc (E))
                   else "")
                & ", created in "
                & GNAT.Source_Info.Enclosing_Entity);

         if Has_Array_Type (E) then
            Create_Validity_Tree_Theory_For_Array (Th, E);
         else
            Create_Validity_Tree_Theory_For_Record (Th, E);
         end if;

         Close_Theory (Th, Kind => Definition_Theory);
      end if;
   end Translate_Type;

end Gnat2Why.Types;
