------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - P O I N T E R S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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

with Ada.Containers;      use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Common_Containers;   use Common_Containers;
with GNAT.Source_Info;
with GNATCOLL.Symbols;    use GNATCOLL.Symbols;
with Namet;               use Namet;
with Sinput;              use Sinput;
with Snames;              use Snames;
with SPARK_Util;          use SPARK_Util;
with VC_Kinds;            use VC_Kinds;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Arrays;      use Why.Gen.Arrays;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Gen.Records;     use Why.Gen.Records;
with Why.Images;          use Why.Images;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

package body Why.Gen.Pointers is

   procedure Declare_Rep_Pointer_Type (P : W_Section_Id; E : Entity_Id)
   with Pre => Is_Access_Type (E);
   --  Similar to Declare_Rep_Record_Type but for pointer types.

   procedure Complete_Rep_Pointer_Type (P : W_Section_Id; E : Entity_Id)
   with Pre => Is_Access_Type (E);
   --  Declares everything for a representative access type but the type and
   --  predefined equality.

   function Get_Rep_Pointer_Module (E : Entity_Id) return W_Module_Id;
   --  Return the name of a record's representative module.

   package Pointer_Typ_To_Roots is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Pointer_Typ_To_Root : Pointer_Typ_To_Roots.Map;
   Completed_Types     : Node_Sets.Set;
   --  Set of representative types for pointers to incomplete or partial types
   --  for which a completion module has been declared.

   type Borrow_Info is record
      Borrowed_Entity : Entity_Id;        --  Root borrowed object
      Borrowed_Expr   : Node_Id;          --  Initial expression
      Borrowed_Ty     : Entity_Id;        --  Type of the borrower
      Pledge_Id       : W_Identifier_Id;  --  Why id for the pledge function
      Pledge_Get      : W_Identifier_Id;  --  Why id for get on pledges
   end record;

   package Borrow_Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Borrow_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Borrow_Infos : Borrow_Info_Maps.Map;
   --  Maps borrowers to their borrowed object and their pledge

   -------------------------------
   -- Complete_Rep_Pointer_Type --
   -------------------------------

   procedure Complete_Rep_Pointer_Type (P : W_Section_Id; E : Entity_Id) is

      procedure Declare_Conversion_Check_Function;
      --  Generate a range predicate and a range check function for E

      procedure Declare_Conversion_Functions;
      --  Generate conversion functions from this type to the root type, and
      --  back.

      procedure Declare_Access_Function;
      --  Generate the predicate related to the access to a pointer value
      --  (cannot access a null pointer).

      procedure Declare_Allocation_Function;
      --  Generate program functions called when allocating deep objects

      ---------------------
      -- Local Variables --
      ---------------------

      Root     : constant Entity_Id := Root_Pointer_Type (E);
      Is_Root  : constant Boolean   := Root = E;
      Ty_Name  : constant W_Name_Id := To_Name (WNE_Rec_Rep);
      Abstr_Ty : constant W_Type_Id := New_Named_Type (Name => Ty_Name);

      A_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      A_Binder : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      ------------------------------
      -- Declare_Access_Functions --
      ------------------------------

      procedure Declare_Access_Function is

         Null_Access_Name : constant String := To_String (WNE_Rec_Comp_Prefix)
         & (Full_Name (E)) & To_String (WNE_Pointer_Value) & "__pred";

         --  The null exclusion defined here is related to the designated type
         --  (that gives the subtype_indication).
         --  This is because the __new_uninitialized_allocator_ is defined
         --  with regard to the the access_type_definition while the
         --  null_exclusion is checked for the subtype_indication.
         --
         --  type Typ is [null_exclusion] access [subtype_indication]
         --  X : Typ := new [subtype_indication]

         Ty        : constant Entity_Id := Etype (E);
         Condition : W_Pred_Id          := True_Pred;
         Top_Field : constant W_Expr_Id := +New_Pointer_Is_Null_Access
           (E, +To_Local (E_Symb (Ty, WNE_Null_Pointer)), Local => True);

         Axiom_Name : constant String :=
           To_String (WNE_Null_Pointer) & "__" & Def_Axiom;

         True_Term : constant W_Term_Id := New_Literal (Value => EW_True);

         Assign_Pointer : constant W_Identifier_Id :=
           To_Local (E_Symb (E, WNE_Assign_Null_Check));

      begin
         --  If the designated type is incomplete, declare a function to access
         --  the designated value. Otherwise, the record field is enough.

         if Designates_Incomplete_Type (E) then
            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_Pointer_Value)),
                     Binders     => A_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => EW_Abstract (Directly_Designated_Type (E)),
                     Def         => New_Call
                       (Domain => EW_Term,
                        Name   => To_Local (E_Symb (E, WNE_Pointer_Open)),
                        Args   =>
                          (1   => New_Record_Access
                               (Name  => +A_Ident,
                                Field => To_Local
                                  (E_Symb (E, WNE_Pointer_Value_Abstr)),
                                Typ   =>
                                  New_Named_Type
                                    (Name => To_Local
                                       (E_Symb (E, WNE_Private_Type))))),
                        Typ    =>
                          EW_Abstract (Directly_Designated_Type (E)))));
         end if;

         Emit (P,
               New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => +New_Identifier (Name => Null_Access_Name),
                  Binders  => A_Binder,
                  Location => No_Location,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => New_Not (Domain => EW_Term,
                                       Right  => +New_Pointer_Is_Null_Access
                                         (E, +A_Ident, Local => True))));

         Emit (P,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => +To_Local (E_Symb (Ty, WNE_Null_Pointer)),
                  Binders     => (1 .. 0 => <>),
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => Abstr_Ty));

         Condition := New_Call (Name => Why_Eq,
                                Args => (1 => +Top_Field, 2 => +True_Term),
                                Typ  => EW_Bool_Type);

         Emit (P,
               New_Axiom (Ada_Node => E,
                          Name     => NID (Axiom_Name),
                          Def      => Condition));

         --  We generate the program access function

         declare
            Post : constant W_Pred_Id :=
              New_Call
                (Name => Why_Eq,
                 Typ  => EW_Bool_Type,
                 Args => (1 => +New_Result_Ident (Why_Empty),
                          2 => +New_Pointer_Value_Access
                            (E, E, +A_Ident, EW_Term, Local => True)));

            Precond : constant W_Pred_Id :=
              New_Call
                (Name => New_Identifier (Name => Null_Access_Name),
                 Args => (1 => +A_Ident));

            Assign_Pointer_Post : constant W_Pred_Id :=
              New_Call
                (Name => Why_Eq,
                 Typ  => EW_Bool_Type,
                 Args => (1 => +New_Result_Ident (Why_Empty),
                          2 => +A_Ident));

         begin
            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => To_Program_Space
                       (To_Local (E_Symb (E, WNE_Pointer_Value))),
                     Binders     => A_Binder,
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => EW_Abstract (Directly_Designated_Type (E)),
                     Pre         => Precond,
                     Post        => Post));

            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => To_Program_Space (Assign_Pointer),
                     Binders     => A_Binder,
                     Return_Type => Abstr_Ty,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Pre         => Precond,
                     Post        => Assign_Pointer_Post));

         end;
      end Declare_Access_Function;

      ---------------------------------
      -- Declare_Allocation_Function --
      ---------------------------------

      procedure Declare_Allocation_Function
      is
         Result   : constant W_Identifier_Id := New_Result_Ident (Why_Empty);
         N_Des_Ty : constant W_Type_Id :=
           Type_Of_Node (Directly_Designated_Type (E));
         Des_Ty   : constant Node_Id := Directly_Designated_Type (E);

         New_Uninitialized_Name : constant W_Identifier_Id :=
           To_Local (E_Symb (E, WNE_Uninit_Allocator));

         New_Initialized_Name : constant W_Identifier_Id :=
           To_Local (E_Symb (E, WNE_Init_Allocator));

         No_Init_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "__void_param", Typ => EW_Unit_Type);

         Init_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "__init_val", Typ  => N_Des_Ty);

         R_No_Init_Binder : constant Binder_Array :=
           (1 => (B_Name => No_Init_Ident, others => <>));

         R_Init_Binder : constant Binder_Array :=
           (1 => (B_Name => Init_Ident, others => <>));

         Result_Null : constant W_Term_Id :=
           +New_Pointer_Is_Null_Access (E, +Result, Local => True);

         Result_Address : constant W_Term_Id :=
           +New_Pointer_Address_Access (E, +Result, Local => True);

         Result_Value : constant W_Term_Id :=
           +New_Pointer_Value_Access (E, E, +Result, EW_Term, Local => True);

         Post_Null : constant W_Expr_Id :=
           New_Not (Domain => EW_Prog, Right => +Result_Null);

         Next_Address : constant W_Identifier_Id := New_Identifier
           (Name => "__next_pointer_address",
            Typ  => EW_Int_Type);

         Post_Address : constant W_Pred_Id := +New_Comparison
           (Symbol => Why_Eq,
            Domain => EW_Prog,
            Left   => +Result_Address,
            Right  => New_Deref (Ada_Node => E,
                                 Right    => Next_Address,
                                 Typ      => EW_Int_Type));

         Post_Value : constant W_Pred_Id := +New_Comparison
           (Symbol => Why_Eq,
            Domain => EW_Prog,
            Left   => +Result_Value,
            Right  => Insert_Simple_Conversion
              (Domain  => EW_Prog,
               Expr    => +Init_Ident,
               To      => EW_Abstract (Des_Ty)));

         Initialized_Post : constant W_Pred_Id := +New_And_Expr
           (Domain => EW_Prog,
            Left   => New_And_Then_Expr (Left   => +Post_Null,
                                         Right  => +Post_Address,
                                         Domain => EW_Prog),
            Right  => +Post_Value);

         Uninitialized_Post : constant W_Pred_Id := +New_And_Then_Expr
           (Domain => EW_Prog,
            Left   => +Post_Null,
            Right  => +Post_Address);

         Address_Effects : constant W_Effects_Id :=
           New_Effects (Writes => (1 => +Next_Address));

      begin

         --  Counter for abstract pointer addresses as global variable
         --  ??? should be incremented
         Emit (P,
               New_Global_Ref_Declaration
                 (Name     => Next_Address,
                  Labels   => Symbol_Sets.Empty_Set,
                  Ref_Type => EW_Int_Type,
                  Location => No_Location));

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => New_Uninitialized_Name,
                  Binders     => R_No_Init_Binder,
                  Return_Type => Abstr_Ty,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Post        => Uninitialized_Post,
                  Effects     => Address_Effects));

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => New_Initialized_Name,
                  Binders     => R_Init_Binder,
                  Return_Type => Abstr_Ty,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Post        => Initialized_Post,
                  Effects     => Address_Effects));

      end Declare_Allocation_Function;

      ---------------------------------------
      -- Declare_Conversion_Check_Function --
      ---------------------------------------

      procedure Declare_Conversion_Check_Function is
         Root_Name  : constant W_Name_Id := To_Why_Type (Root);
         Root_Abstr : constant W_Type_Id :=
           +New_Named_Type (Name => Root_Name);
         Des_Ty     : constant Entity_Id :=
           Retysp (Directly_Designated_Type (E));

         R_Ident    : constant W_Identifier_Id :=
           New_Identifier (Name => "r", Typ => Root_Abstr);
         R_Val      : constant W_Expr_Id :=
           New_Pointer_Value_Access
             (Ada_Node => Empty,
              E        => Root,
              Name     => +R_Ident,
              Domain   => EW_Term);
         Post       : constant W_Pred_Id :=
           New_Call
             (Name => Why_Eq,
              Typ  => EW_Bool_Type,
              Args => (+New_Result_Ident (Why_Empty), +R_Ident));
         Num        : constant Positive :=
           (if Has_Array_Type (Des_Ty) then
                 2 * Positive (Number_Dimensions (Des_Ty))
            else Count_Discriminants (Des_Ty));
         --  For arrays the range check function takes as parameters the
         --  expression and the bounds for Des_Ty. For records it should take
         --  the discriminants.

         R_Binder   : Binder_Array (1 .. Num + 1);
         Args       : W_Expr_Array (1 .. Num + 1);
         Pre_Cond   : W_Pred_Id;
         Check_Pred : W_Pred_Id := True_Pred;

      begin
         R_Binder (Num + 1) :=
           Binder_Type'(B_Name => R_Ident,
                        others => <>);
         Args (Num + 1) := +R_Ident;

         if Has_Array_Type (Des_Ty) then
            pragma Assert
              (not Is_Constrained (Retysp (Directly_Designated_Type (Root))));
            pragma Assert (Is_Constrained (Des_Ty));

            --  Get names and binders for Des_Ty bounds

            for Count in 1 .. Positive (Number_Dimensions (Des_Ty)) loop
               Args (2 * Count - 1) := +To_Local
                 (E_Symb (Des_Ty, WNE_Attr_First (Count)));
               Args (2 * Count) := +To_Local
                 (E_Symb (Des_Ty, WNE_Attr_Last (Count)));
               R_Binder (2 * Count - 1) :=
                 Binder_Type'
                   (B_Name => +Args (2 * Count - 1),
                    others => <>);
               R_Binder (2 * Count) :=
                 Binder_Type'
                   (B_Name => +Args (2 * Count),
                    others => <>);
            end loop;

            --  Check that the bounds of R_Val match the bounds of Des_Ty

            Check_Pred :=
              +New_Bounds_Equality
                (R_Val, Args (1 .. Num),
                 Dim => Positive (Number_Dimensions (Des_Ty)));
         else

            --  We handle records with discriminants here by calling the range
            --  check functions for records.

            pragma Assert (Has_Discriminants (Des_Ty));
            pragma Assert
              (not Is_Constrained (Retysp (Directly_Designated_Type (Root))));
            pragma Assert (Is_Constrained (Des_Ty));

            declare
               Discr : Entity_Id := First_Discriminant (Des_Ty);
            begin
               for Count in 1 .. Num loop
                  Args (Count) := +To_Why_Id
                    (Discr,
                     Local => True,
                     Rec   => Root,
                     Typ   => Base_Why_Type (Etype (Discr)));
                  R_Binder (Count) :=
                    Binder_Type'
                      (B_Name => +Args (Count),
                       others => <>);
                  Next_Discriminant (Discr);
               end loop;
               pragma Assert (No (Discr));
            end;

            Check_Pred :=
              New_Call
                (Name => E_Symb (Des_Ty, WNE_Range_Pred),
                 Args => Args (1 .. Num) & R_Val,
                 Typ  => EW_Bool_Type);
         end if;

         --  Do subtype check only if the pointer is not null

         Check_Pred :=
           New_Conditional
             (Condition => New_Not
                (Domain => EW_Pred,
                 Right  => New_Pointer_Is_Null_Access
                   (E     => Root,
                    Name  => +R_Ident)),
              Then_Part => +Check_Pred,
              Typ       => EW_Bool_Type);

         Emit (P,
               New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => To_Local (E_Symb (E, WNE_Range_Pred)),
                  Location => Safe_First_Sloc (E),
                  Labels   => Symbol_Sets.Empty_Set,
                  Binders  => R_Binder,
                  Def      => +Check_Pred));
         Pre_Cond :=
           New_Call (Name => To_Local (E_Symb (E, WNE_Range_Pred)),
                     Args => Args);
         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => To_Local (E_Symb (E, WNE_Range_Check_Fun)),
                  Binders     => R_Binder,
                  Location    => Safe_First_Sloc (E),
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => Root_Abstr,
                  Pre         => Pre_Cond,
                  Post        => Post));
      end Declare_Conversion_Check_Function;

      ----------------------------------
      -- Declare_Conversion_Functions --
      ----------------------------------

      procedure Declare_Conversion_Functions is
         R_Ident   : constant W_Identifier_Id :=
           New_Identifier (Name => "r", Typ => EW_Abstract (Root));
         R_Binder  : constant Binder_Array :=
           (1 => (B_Name => R_Ident,
                  others => <>));

      begin
         declare
            Root_Ty : constant W_Type_Id := EW_Abstract (Root);
            Def     : constant W_Expr_Id :=
              Pointer_From_Split_Form
                (A  =>
                   (1 => Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => New_Pointer_Value_Access
                         (Ada_Node       => Empty,
                          E              => E,
                          Name           => +A_Ident,
                          Domain         => EW_Term,
                          Local          => True),
                       To             =>
                         EW_Abstract
                           (Directly_Designated_Type (Root)),
                       Force_No_Slide => True),
                    2 => New_Pointer_Address_Access
                      (E     => E,
                       Name  => +A_Ident,
                       Local => True),
                    3 => New_Pointer_Is_Null_Access
                      (E     => E,
                       Name  => +A_Ident,
                       Local => True)),
                 Ty => Root);
            --  (value   = to_root a.value,
            --   addr    = a.addr,
            --   is_null = a.is_null)

         begin
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_To_Base)),
                  Binders     => A_Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => Root_Ty,
                  Def         => Def));
         end;

         declare
            Def : constant W_Expr_Id :=
              Pointer_From_Split_Form
                (A     =>
                   (1 => Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => New_Pointer_Value_Access
                         (Ada_Node       => Empty,
                          E              => Root,
                          Name           => +R_Ident,
                          Domain         => EW_Term),
                       To             =>
                         EW_Abstract
                           (Directly_Designated_Type (E)),
                       Force_No_Slide => True),
                    2 => New_Pointer_Address_Access
                      (E     => Root,
                       Name  => +R_Ident),
                    3 => New_Pointer_Is_Null_Access
                      (E     => Root,
                       Name  => +R_Ident)),
                 Ty    => E,
                 Local => True);
            --  (value   = to_e r.value,
            --   addr    = r.addr,
            --   is_null = r.is_null)

         begin
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Of_Base)),
                  Binders     => R_Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => Abstr_Ty,
                  Def         => Def));
         end;
      end Declare_Conversion_Functions;

   --  Start of processing for Complete_Rep_Pointer_Type

   begin
      Declare_Access_Function;
      Declare_Allocation_Function;

      if not Is_Root then
         Declare_Conversion_Functions;
         Declare_Conversion_Check_Function;
      else

         --  Declare dummy conversion functions that will be used to convert
         --  other types which use E as a representative type.

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Of_Base)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
      end if;
   end Complete_Rep_Pointer_Type;

   -----------------------------------------
   -- Create_Rep_Pointer_Theory_If_Needed --
   -----------------------------------------

   procedure Create_Rep_Pointer_Theory_If_Needed
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Ancestor : constant Entity_Id := Repr_Pointer_Type (E);

   begin
      if Ancestor /= Empty then
         return;
      end if;

      Pointer_Typ_To_Root.Insert (Retysp (Directly_Designated_Type (E)), E);

      Open_Theory
        (P, Get_Rep_Pointer_Module (E),
         Comment =>
           "Module for axiomatizing the pointer theory associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Declare_Rep_Pointer_Type (P, E);

      Close_Theory (P, Kind => Definition_Theory, Defined_Entity => E);
   end Create_Rep_Pointer_Theory_If_Needed;

   -------------------------
   -- Declare_Ada_Pointer --
   -------------------------

   procedure Declare_Ada_Pointer (P : W_Section_Id; E : Entity_Id) is
      Rep_Module : constant W_Module_Id := Get_Rep_Pointer_Module (E);

   begin
      --  Export the theory containing the pointer record definition.

      Add_With_Clause (P, Rep_Module, EW_Export);

      --  Rename the representative record type as expected.

      Emit (P, New_Type_Decl (Name  => To_Why_Type (E, Local => True),
                              Alias => +New_Named_Type
                                (Name => To_Name (WNE_Rec_Rep))));
      Emit
        (P,
         Why.Atree.Builders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (E_Symb (E, WNE_Dummy)),
            Binders     => (1 .. 0 => <>),
            Labels      => Symbol_Sets.Empty_Set,
            Location    => No_Location,
            Return_Type =>
              +New_Named_Type (Name => To_Why_Type (E, Local => True))));
   end Declare_Ada_Pointer;

   ------------------------
   -- Declare_Pledge_Ref --
   ------------------------

   procedure Declare_Pledge_Ref (File : W_Section_Id; E : Entity_Id)
   is
      Current_Module  : constant W_Module_Id := E_Module (E);
      Pledge_Ty_Name  : constant String := "__pledge_ty";
      Pledge_Name     : constant String := Full_Name (E) & "__pledge";
      Pledge_Get_Name : constant String := "__pledge_get";
      Ref_Type        : constant W_Type_Id :=
        New_Named_Type (New_Name (Symb   => NID (Pledge_Ty_Name),
                                  Module => Current_Module));
      Borrowed_Expr   : Node_Id := Expression (Enclosing_Declaration (E));
      Borrowed_Ty     : Entity_Id := Etype (E);
      Borrowed_Entity : Entity_Id;
      Cur             : Node_Id := Expression (Enclosing_Declaration (E));

   begin
      --  Find the borrowed initial expression and type.
      --  We go over the initial expression to find the biggest prefix
      --  containing no function calls and we store it in Borrowed_Expr.
      --  Borrowed_Ty is the type of the object borrowing the expression at
      --  this point (either E or the first formal of a call to a traversal
      --  function).

      loop
         case Nkind (Cur) is
            when N_Identifier | N_Expanded_Name =>
               Borrowed_Entity := Entity (Cur);
               exit;
            when N_Selected_Component
               | N_Indexed_Component
               | N_Slice
               | N_Explicit_Dereference
            =>
               Cur := Prefix (Cur);
            when N_Qualified_Expression
               | N_Type_Conversion
               | N_Unchecked_Type_Conversion
            =>
               Cur := Expression (Cur);
            when N_Function_Call =>
               Borrowed_Expr := First_Actual (Cur);
               Borrowed_Ty := Etype (First_Formal (Get_Called_Entity (Cur)));
               Cur := Borrowed_Expr;
               pragma Assert (Present (Borrowed_Expr));
            when others =>
               raise Not_Implemented;
         end case;
      end loop;

      --  Clone the pledge module. It creates a pledge function relating the
      --  borrowed entity and the borrower. We could have chosen to rather
      --  relate the borrowed expression and the borrower, but it makes it
      --  less practical to have good triggers for quantified expressions
      --  arising from the translation of a call to a function which has a
      --  pledge annotation.

      Emit (File,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               As_Name       => No_Symbol,
               Origin        => Pledge,
               Substitutions =>
                 (1 => New_Clone_Substitution
                      (Kind      => EW_Type_Subst,
                       Orig_Name => New_Name
                         (Symb => NID ("borrower")),
                       Image     => Get_Name (Type_Of_Node (Etype (E)))),
                  2 => New_Clone_Substitution
                      (Kind      => EW_Type_Subst,
                       Orig_Name => New_Name
                         (Symb => NID ("borrowed")),
                       Image     => Get_Name
                         (Type_Of_Node (Borrowed_Entity))))));

      declare
         Loc_Pledge_Id : constant W_Identifier_Id :=
           New_Identifier (Symb   => NID (Pledge_Name),
                           Typ    => New_Named_Type (Pledge_Ty_Name),
                           Domain => EW_Prog);
         Pledge_Id     : constant W_Identifier_Id :=
           New_Identifier (Symb   => NID (Pledge_Name),
                           Module => Current_Module,
                           Typ    => Ref_Type,
                           Domain => EW_Prog);
         Pledge_Get_Id : constant W_Identifier_Id :=
           New_Identifier (Symb   => NID (Pledge_Get_Name),
                           Module => Current_Module,
                           Typ    => EW_Bool_Type,
                           Domain => EW_Prog);
      begin
         Emit (File,
               New_Global_Ref_Declaration (Name     => Loc_Pledge_Id,
                                           Ref_Type => Get_Typ (Loc_Pledge_Id),
                                           Labels   => Symbol_Sets.Empty_Set,
                                           Location => No_Location));

         Borrow_Infos.Insert
           (E, Borrow_Info'(Borrowed_Entity => Borrowed_Entity,
                            Borrowed_Expr   => Borrowed_Expr,
                            Borrowed_Ty     => Borrowed_Ty,
                            Pledge_Id       => Pledge_Id,
                            Pledge_Get      => Pledge_Get_Id));
      end;
   end Declare_Pledge_Ref;

   -------------------------------
   -- Declare_Rep_Pointer_Compl --
   -------------------------------

   procedure Declare_Rep_Pointer_Compl_If_Needed
     (P : W_Section_Id; E : Entity_Id)
   is
      Inserted : Boolean;
      Position : Node_Sets.Cursor;

   begin
      --  Use the Completed_Types set to make sure that we do not complete the
      --  same type twice.

      Completed_Types.Insert (E, Position, Inserted);

      if Inserted then
         Open_Theory
           (P, E_Compl_Module (E),
            Comment =>
              "Module for completing the pointer theory associated to type "
            & """" & Get_Name_String (Chars (E)) & """"
            & (if Sloc (E) > 0 then
                 " defined at " & Build_Location_String (Sloc (E))
              else "")
            & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Add_With_Clause (P, Get_Rep_Pointer_Module (E), EW_Import);

         Emit (P,
               New_Clone_Declaration
                 (Theory_Kind   => EW_Module,
                  Clone_Kind    => EW_Export,
                  As_Name       => No_Symbol,
                  Origin        => Access_To_Incomp_Ty,
                  Substitutions =>
                    (1 => New_Clone_Substitution
                         (Kind      => EW_Type_Subst,
                          Orig_Name => New_Name
                            (Symb => NID ("abstr_ty")),
                          Image     => To_Local (Get_Name
                            (E_Symb (E, WNE_Private_Type)))),
                     2 => New_Clone_Substitution
                       (Kind      => EW_Type_Subst,
                        Orig_Name => New_Name
                          (Symb => NID ("comp_ty")),
                        Image     =>
                          Get_Name
                            (EW_Abstract (Directly_Designated_Type (E)))))));

         Complete_Rep_Pointer_Type (P, E);

         Close_Theory (P, Kind => Definition_Theory, Defined_Entity => E);
      end if;
   end Declare_Rep_Pointer_Compl_If_Needed;

   ------------------------------
   -- Declare_Rep_Pointer_Type --
   ------------------------------

   procedure Declare_Rep_Pointer_Type (P : W_Section_Id; E : Entity_Id) is

      procedure Declare_Equality_Function;
      --  Generate the boolean equality function for the pointer type
      --  Comparing pointer equality is equivalent to comparing their addresses
      --  Equal pointers have equal values

      procedure Declare_Pointer_Type;
      --  Emit the why record declaration related to the ada pointer type

      ---------------------
      -- Local Variables --
      ---------------------

      Ty_Name   : constant W_Name_Id  := To_Name (WNE_Rec_Rep);
      Abstr_Ty  : constant W_Type_Id  := New_Named_Type (Name => Ty_Name);
      Value_Id  : constant W_Identifier_Id :=
        (if Designates_Incomplete_Type (E)
         then W_Identifier_Id'(New_Identifier
           (Symb =>
              Get_Symb (Get_Name (E_Symb (E, WNE_Pointer_Value_Abstr))),
            Domain => EW_Term,
            Typ    =>
              New_Named_Type
                (To_Local (Get_Name (E_Symb (E, WNE_Private_Type))))))
         else To_Local (E_Symb (E, WNE_Pointer_Value)));

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      A_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      --------------------------
      -- Declare_Pointer_Type --
      --------------------------

      procedure Declare_Pointer_Type is
         Binders_F : Binder_Array (1 .. 3);
         Ty_Name   : constant W_Name_Id := To_Name (WNE_Rec_Rep);

      begin
         pragma Assert (not Has_Private_Type (E));
         Binders_F (1) :=
           (B_Name => To_Local (E_Symb (E, WNE_Is_Null_Pointer)),
            Labels => Get_Model_Trace_Label ("'" & Is_Null_Label),
            others => <>);

         Binders_F (2) :=
           (B_Name => To_Local (E_Symb (E, WNE_Pointer_Address)),
            others => <>);

         Binders_F (3) :=
           (B_Name => Value_Id,
            Labels => Get_Model_Trace_Label ("'" & All_Label),
            others => <>);

         Emit_Record_Declaration (Section      => P,
                                  Name         => Ty_Name,
                                  Binders      => Binders_F,
                                  SPARK_Record => True);

         Emit_Ref_Type_Definition
           (File => P,
            Name => Ty_Name);

         Emit (P, New_Havoc_Declaration (Ty_Name));
      end Declare_Pointer_Type;

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function is
         B_Ident            : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);

         Sec_Condition      : W_Expr_Id;

         Comparison_Address : constant W_Pred_Id :=
           +New_Comparison
           (Domain => EW_Pred,
            Symbol => Why_Eq,
            Left   => +New_Pointer_Address_Access (E, +A_Ident, Local => True),
            Right  => +New_Pointer_Address_Access (E, +B_Ident, Local => True)
           );

         Comparison_Null    : constant W_Pred_Id :=
           +New_Comparison
           (Domain => EW_Pred,
            Symbol => Why_Eq,
            Left   => +New_Pointer_Is_Null_Access (E, +A_Ident, Local => True),
            Right  => +New_Pointer_Is_Null_Access (E, +B_Ident, Local => True)
           );

         Comparison_Value  : constant W_Pred_Id :=
           +New_Comparison
           (Domain => EW_Pred,
            Symbol => Why_Eq,
            Left   => New_Record_Access
              (Name  => +A_Ident,
               Field => Value_Id,
               Typ   => Get_Typ (Value_Id)),
            Right  => New_Record_Access
              (Name  => +B_Ident,
               Field => Value_Id,
               Typ   => Get_Typ (Value_Id))
           );

      begin
         --  Compare Pointer_Address field and assume pointer value equality if
         --  addresses are equal.

         Sec_Condition := New_Conditional
           (Domain    => EW_Pred,
            Condition => New_Not (Domain => EW_Pred,
                                  Right  => +New_Pointer_Is_Null_Access
                                    (E, +A_Ident, Local => True)),
            Then_Part => +New_And_Expr (Left   => +Comparison_Address,
                                        Right  => +Comparison_Value,
                                        Domain => EW_Pred));

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Bool_Eq)),
               Binders     => A_Binder &
                 Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                 others => <>)),
               Return_Type => +EW_Bool_Type,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Def         =>
                 +New_And_Expr
                    (+Comparison_Null, +Sec_Condition, EW_Pred)));
      end Declare_Equality_Function;

   --  Start of processing for Declare_Rep_Pointer_Type

   begin
      --  For types designating incomplete types, declare a new uninterpreted
      --  type for the value component.

      if Designates_Incomplete_Type (E) then
         Emit (P,
               New_Type_Decl
                 (Name => Img
                    (Get_Symb (To_Local (E_Symb (E, WNE_Private_Type)))))
              );
      end if;

      Declare_Pointer_Type;
      Declare_Equality_Function;

      if not Designates_Incomplete_Type (E) then
         Complete_Rep_Pointer_Type (P, E);
      end if;
   end Declare_Rep_Pointer_Type;

   -------------------------
   -- Get_Borrowed_Entity --
   -------------------------

   function Get_Borrowed_Entity (E : Entity_Id) return Entity_Id is
     (Borrow_Infos (E).Borrowed_Entity);

   -----------------------
   -- Get_Borrowed_Expr --
   -----------------------

   function Get_Borrowed_Expr (E : Entity_Id) return Node_Id is
     (Borrow_Infos (E).Borrowed_Expr);

   ---------------------
   -- Get_Borrowed_Ty --
   ---------------------

   function Get_Borrowed_Typ (E : Entity_Id) return Entity_Id is
     (Borrow_Infos (E).Borrowed_Ty);

   -------------------
   -- Get_Pledge_Id --
   -------------------

   function Get_Pledge_Id (E : Entity_Id) return W_Identifier_Id is
     (Borrow_Infos (E).Pledge_Id);

   ----------------------------
   -- Get_Rep_Pointer_Module --
   ----------------------------

   function Get_Rep_Pointer_Module (E : Entity_Id) return W_Module_Id is
      Ancestor : constant Entity_Id := Repr_Pointer_Type (E);
      Name     : constant String    :=
        Full_Name (Ancestor) & To_String (WNE_Rec_Rep);

   begin
      return New_Module (File => No_Symbol,
                         Name => Name);
   end Get_Rep_Pointer_Module;

   ----------------------------------
   -- Insert_Pointer_Subtype_Check --
   ----------------------------------

   function Insert_Pointer_Subtype_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id
   is
      Root   : constant Entity_Id := Root_Pointer_Type (Check_Ty);
      Des_Ty : constant Entity_Id :=
        Retysp (Directly_Designated_Type (Retysp (Check_Ty)));

   begin
      if not Is_Constrained (Des_Ty) or else Is_Constrained (Root) then
         return Expr;
      else
         return
           +New_VC_Call
             (Ada_Node => Ada_Node,
              Name     => E_Symb (Check_Ty, WNE_Range_Check_Fun),
              Progs    =>
                Prepare_Args_For_Access_Subtype_Check (Check_Ty, +Expr),
              Reason   => (if Has_Array_Type (Des_Ty) then VC_Range_Check
                           else VC_Discriminant_Check),
              Domain   => EW_Prog,
              Typ      => Get_Type (+Expr));
      end if;
   end Insert_Pointer_Subtype_Check;

   ----------------------------
   -- New_Ada_Pointer_Update --
   ----------------------------

   function New_Ada_Pointer_Update
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id)
      return W_Expr_Id
   is
      Tmp : constant W_Expr_Id := New_Temp_For_Expr (Name);
      Ty  : constant Entity_Id := Get_Ada_Node (+Get_Type (Name));
      T   : W_Expr_Id;

      Selected_Field : constant W_Identifier_Id :=
        (if Designates_Incomplete_Type (Repr_Pointer_Type (Ty))
         then E_Symb (Ty, WNE_Pointer_Value_Abstr)
         else E_Symb (Ty, WNE_Pointer_Value));

      --  If Ty designates an incomplete type, we need to reconstruct the
      --  abstract value.

      Rec_Val     : constant W_Expr_Id :=
        (if Designates_Incomplete_Type (Repr_Pointer_Type (Ty))
         then New_Call
           (Domain => Domain,
            Name   => E_Symb (Ty, WNE_Pointer_Close),
            Args   => (1 => Value))
         else Value);
      Update_Expr : constant W_Expr_Id :=
          New_Record_Update
               (Ada_Node => Ada_Node,
                Name     => Tmp,
                Updates  =>
                  (1 => New_Field_Association
                     (Domain => Domain,
                      Field  => Selected_Field,
                      Value  => Rec_Val)),
                Typ      => Get_Type (Name));

   begin
      if Domain = EW_Prog then
         T := +Sequence
           (+New_Ignore
              (Ada_Node => Ada_Node,
               Prog     => +New_Pointer_Value_Access (Ada_Node => Ada_Node,
                                                      E        => Ty,
                                                      Name     => Tmp,
                                                      Domain   => Domain)),
            +Update_Expr);
      else
         T := Update_Expr;
      end if;

      return Binding_For_Temp (Ada_Node, Domain, Tmp, T);
   end New_Ada_Pointer_Update;

   ---------------------
   -- New_Pledge_Call --
   ---------------------

   function New_Pledge_Call
     (E            : Entity_Id;
      Borrowed_Arg : W_Expr_Id;
      Brower_Arg   : W_Expr_Id) return W_Expr_Id
   is
      Pledge_Id  : constant W_Identifier_Id :=
        Borrow_Infos (E).Pledge_Id;
      Pledge_Get : constant W_Identifier_Id :=
        Borrow_Infos (E).Pledge_Get;
      Pledge_Deref : constant W_Expr_Id :=
        New_Deref (Right => Pledge_Id, Typ => Get_Typ (Pledge_Id));
   begin
      return New_Call
        (Domain => EW_Term,
         Name   => Pledge_Get,
         Args   => (Pledge_Deref, Borrowed_Arg, Brower_Arg),
         Typ    => Get_Typ (Pledge_Id));
   end New_Pledge_Call;

   -----------------------
   -- New_Pledge_Update --
   -----------------------

   function New_Pledge_Update
     (E           : Entity_Id;
      Borrowed_Id : W_Identifier_Id;
      Brower_Id   : W_Identifier_Id;
      Def         : W_Term_Id) return W_Prog_Id
   is
      Pledge_Id  : constant W_Identifier_Id :=
        Borrow_Infos (E).Pledge_Id;
      Pledge_Get : constant W_Identifier_Id :=
        Borrow_Infos (E).Pledge_Get;
      Res        : constant W_Identifier_Id :=
        New_Result_Ident (Typ => Get_Typ (Pledge_Id));
      Res_Acc    : constant W_Term_Id :=
        New_Call (Name => Pledge_Get,
                  Args => (+Res, +Borrowed_Id, +Brower_Id),
                  Typ  => EW_Bool_Type);
   begin
      return New_Assignment
        (Name   => Pledge_Id,
         Value  => New_Any_Expr
           (Post        => New_Universal_Quantif
                (Binders  => (1 => Binder_Type'(B_Name => Borrowed_Id,
                                                others => <>),
                              2 => Binder_Type'(B_Name => Brower_Id,
                                                others => <>)),
                 Triggers => New_Triggers
                   (Triggers => (1 => New_Trigger (Terms => (1 => +Res_Acc)))),
                 Pred     => +New_Comparison
                   (Symbol => Why_Eq,
                    Left   => +Res_Acc,
                    Right  => +Def,
                    Domain => EW_Pred)),
            Return_Type => Get_Typ (Pledge_Id),
            Labels      => Symbol_Sets.Empty_Set),
         Typ    => Get_Typ (Pledge_Id),
         Labels => Symbol_Sets.Empty_Set);
   end New_Pledge_Update;

   --------------------------------
   -- New_Pointer_Address_Access --
   --------------------------------

   function New_Pointer_Address_Access
     (E     : Entity_Id;
      Name  : W_Expr_Id;
      Local : Boolean := False)
      return W_Expr_Id
   is
      Field : constant W_Identifier_Id :=
        (if Local
         then To_Local (E_Symb (E, WNE_Pointer_Address))
         else E_Symb (E, WNE_Pointer_Address));

   begin
      return New_Record_Access (Name  => +Name,
                                Field => Field,
                                Typ   => EW_Int_Type);
   end New_Pointer_Address_Access;

   --------------------------------
   -- New_Pointer_Is_Null_Access --
   --------------------------------

   function New_Pointer_Is_Null_Access
     (E     : Entity_Id;
      Name  : W_Expr_Id;
      Local : Boolean := False)
      return W_Expr_Id
   is
      Field : constant W_Identifier_Id :=
        (if Local
         then To_Local (E_Symb (E, WNE_Is_Null_Pointer))
         else E_Symb (E, WNE_Is_Null_Pointer));

   begin
      return New_Record_Access (Name  => +Name,
                                Field => Field,
                                Typ   => EW_Bool_Type);
   end New_Pointer_Is_Null_Access;

   ------------------------------
   -- New_Pointer_Value_Access --
   ------------------------------

   function New_Pointer_Value_Access
     (Ada_Node : Node_Id;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain;
      Local    : Boolean := False)
      return W_Expr_Id
   is
      Field : constant W_Identifier_Id :=
        (if Local
         then To_Local (E_Symb (E, WNE_Pointer_Value))
         else E_Symb (E, WNE_Pointer_Value));

   begin
      if Domain = EW_Prog then
         return
           +New_VC_Call
           (Ada_Node => Ada_Node,
            Name     => To_Program_Space (Field),
            Progs    => (1 => +Name),
            Domain   => EW_Prog,
            Reason   => VC_Null_Pointer_Dereference,
            Typ      => EW_Abstract (Directly_Designated_Type (Retysp (E))));
      elsif Designates_Incomplete_Type (Repr_Pointer_Type (Retysp (E))) then
         return New_Call (Args   => (1 => Name),
                          Name   => Field,
                          Domain => Domain,
                          Typ    => EW_Abstract
                            (Directly_Designated_Type (Retysp (E))));
      else
         return New_Record_Access (Name  => +Name,
                                   Field => Field,
                                   Typ   => EW_Abstract
                                     (Directly_Designated_Type (Retysp (E))));
      end if;
   end New_Pointer_Value_Access;

   -------------------------------------------
   -- Prepare_Args_For_Access_Subtype_Check --
   -------------------------------------------

   function Prepare_Args_For_Access_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id)
      return W_Expr_Array
   is
      Des_Ty : constant Entity_Id :=
        Retysp (Directly_Designated_Type (Retysp (Check_Ty)));

   begin
      --  Parameters of the range check function for arrays are the bounds of
      --  Check_Ty and Expr.

      if Is_Array_Type (Des_Ty) then
         declare
            Dim  : constant Positive := Positive (Number_Dimensions (Des_Ty));
            Args : W_Expr_Array (1 .. Dim * 2 + 1);
         begin

            Args (Dim * 2 + 1) := +Expr;
            for Count in 1 .. Dim loop
               Args (2 * Count - 1) :=
                 Get_Array_Attr (Domain => EW_Term,
                                 Ty     => Des_Ty,
                                 Attr   => Attribute_First,
                                 Dim    => Count);
               Args (2 * Count) :=
                 Get_Array_Attr (Domain => EW_Term,
                                 Ty     => Des_Ty,
                                 Attr   => Attribute_Last,
                                 Dim    => Count);
            end loop;
            return Args;
         end;

      --  Use Prepare_Args_For_Subtype_Check on designated type for records

      else
         pragma Assert (Has_Discriminants (Des_Ty));
         return Prepare_Args_For_Subtype_Check (Des_Ty, Expr);
      end if;
   end Prepare_Args_For_Access_Subtype_Check;

   -----------------------------
   -- Pointer_From_Split_Form --
   -----------------------------

   function Pointer_From_Split_Form
     (I           : Item_Type;
      Ref_Allowed : Boolean)
      return W_Expr_Id
   is
      E       : constant Entity_Id := I.Value.Ada_Node;
      Ty      : constant Entity_Id := Etype (E);
      Value   : W_Expr_Id;
      Addr    : W_Expr_Id;
      Is_Null : W_Expr_Id;

   begin
      if I.Value.Mutable and then Ref_Allowed then
         Value := New_Deref
           (E, I.Value.B_Name, Get_Typ (I.Value.B_Name));
      else
         Value := +I.Value.B_Name;
      end if;

      if I.Mutable and then Ref_Allowed then
         Addr := New_Deref (E, I.Address, Get_Typ (I.Address));
         Is_Null := New_Deref (E, I.Is_Null, Get_Typ (I.Is_Null));
      else
         Addr := +I.Address;
         Is_Null := +I.Is_Null;
      end if;

      return Pointer_From_Split_Form
        (Ada_Node => E,
         A        => (1 => Value, 2 => Addr, 3 => Is_Null),
         Ty       => Ty);
   end Pointer_From_Split_Form;

   function Pointer_From_Split_Form
     (Ada_Node : Node_Id := Empty;
      A        : W_Expr_Array;
      Ty       : Entity_Id;
      Local    : Boolean := False)
      return W_Expr_Id
   is
      Ty_Ext    : constant Entity_Id := Retysp (Ty);
      Value     : W_Expr_Id := A (1);
      Addr      : constant W_Expr_Id := A (2);
      Is_Null   : constant W_Expr_Id := A (3);
      S_Value   : W_Identifier_Id :=
        (if Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext))
         then E_Symb (Ty_Ext, WNE_Pointer_Value_Abstr)
         else E_Symb (Ty_Ext, WNE_Pointer_Value));
      S_Addr    : W_Identifier_Id := E_Symb (Ty_Ext, WNE_Pointer_Address);
      S_Is_Null : W_Identifier_Id := E_Symb (Ty_Ext, WNE_Is_Null_Pointer);

   begin
      --  If Local use local names for fields of Ty

      if Local then
         S_Value := To_Local (S_Value);
         S_Addr := To_Local (S_Addr);
         S_Is_Null := To_Local (S_Is_Null);
      end if;

      --  If Ty designates an incomplete type, we need to reconstruct the
      --  abstract value.

      if Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext)) then
         Value := New_Call
           (Domain => EW_Term,
            Name   =>
              (if Local then To_Local (E_Symb (Ty_Ext, WNE_Pointer_Close))
               else E_Symb (Ty_Ext, WNE_Pointer_Close)),
            Args   => (1 => Value));
      end if;

      return New_Record_Aggregate
        (Ada_Node     => Ada_Node,
         Associations =>
           (1 => New_Field_Association
                (Domain => EW_Term,
                 Field  => S_Value,
                 Value  => Value),
            2 => New_Field_Association
                (Domain => EW_Term,
                 Field  => S_Addr,
                 Value  => Addr),
            3 => New_Field_Association
                (Domain => EW_Term,
                 Field  => S_Is_Null,
                 Value  => Is_Null)),
         Typ          => EW_Abstract (Ty_Ext));
   end Pointer_From_Split_Form;

   -----------------------
   -- Repr_Pointer_Type --
   -----------------------

   function Repr_Pointer_Type (E : Entity_Id) return Entity_Id is
      use Pointer_Typ_To_Roots;

      C : constant Pointer_Typ_To_Roots.Cursor :=
        Pointer_Typ_To_Root.Find
          (Retysp (Directly_Designated_Type (Retysp (E))));

   begin
      if Has_Element (C) then
         return Pointer_Typ_To_Root (C);
      else
         return Empty;
      end if;
   end Repr_Pointer_Type;

   -----------------------
   -- Root_Pointer_Type --
   -----------------------

   function Root_Pointer_Type (E : Entity_Id) return Entity_Id is
   begin
      return Repr_Pointer_Type (Root_Retysp (E));
   end Root_Pointer_Type;

end Why.Gen.Pointers;
