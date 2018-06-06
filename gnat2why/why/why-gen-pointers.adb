------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - P O I N T E R S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2018, AdaCore                        --
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

with Ada.Containers;             use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Common_Containers;          use Common_Containers;
with GNAT.Source_Info;
with Gnat2Why.Expr;              use Gnat2Why.Expr;
with Namet;                      use Namet;
with Sinput;                     use Sinput;
with SPARK_Atree;                use SPARK_Atree;
with SPARK_Util;                 use SPARK_Util;
with SPARK_Util.Types;           use SPARK_Util.Types;
with VC_Kinds;                   use VC_Kinds;
with Why.Atree.Accessors;        use Why.Atree.Accessors;
with Why.Atree.Builders;         use Why.Atree.Builders;
with Why.Atree.Modules;          use Why.Atree.Modules;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Binders;            use Why.Gen.Binders;
with Why.Gen.Decl;               use Why.Gen.Decl;
with Why.Gen.Expr;               use Why.Gen.Expr;
with Why.Gen.Names;              use Why.Gen.Names;
with Why.Gen.Preds;              use Why.Gen.Preds;
with Why.Gen.Progs;              use Why.Gen.Progs;
with Why.Gen.Records;            use Why.Gen.Records;
with Why.Inter;                  use Why.Inter;
with Why.Types;                  use Why.Types;

package body Why.Gen.Pointers is

   procedure Declare_Conversion_Check_Function
     (Section : W_Section_Id;
      E       : Entity_Id;
      Root    : Entity_Id)
   with Pre => Has_Discriminants (Directly_Designated_Type (E));
   --  Generate the program function which is used to insert subtype
   --  discriminant checks.

   procedure Declare_Rep_Pointer_Type (P : W_Section_Id; E : Entity_Id);
   --  Similar to Declare_Rep_Record_Type but for pointer types.

   function Get_Rep_Pointer_Module (E : Entity_Id) return W_Module_Id;
   --  Return the name of a record's representative module.

   package Pointer_Typ_To_Roots is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Pointer_Typ_To_Root : Pointer_Typ_To_Roots.Map :=
     Pointer_Typ_To_Roots.Empty_Map;

   -------------------------
   -- Declare_Ada_Pointer --
   -------------------------

   procedure Declare_Ada_Pointer (P : W_Section_Id; E : Entity_Id) is
      Rep_Module : constant W_Module_Id := Get_Rep_Pointer_Module (E);
      Root       : constant Entity_Id := Root_Pointer_Type (E);

   begin
      --  Export the theory containing the pointer record definition.

      Add_With_Clause (P, Rep_Module, EW_Export);

      --  Rename the representative record type as expected.

      Emit (P, New_Type_Decl (Name  => To_Why_Type (E, Local => True),
                              Alias => +New_Named_Type
                                (Name => To_Name (WNE_Rec_Rep))));

      if Root /= E
        and then Has_Discriminants (Directly_Designated_Type (E))
        and then Is_Constrained (Directly_Designated_Type (E))
      then
         Declare_Conversion_Check_Function (P, E, Root);
      end if;
   end Declare_Ada_Pointer;

   ---------------------------------
   -- Declare_Allocation_Function --
   ---------------------------------

   procedure Declare_Allocation_Function (E : Entity_Id; File : W_Section_Id)
   is
      Ty_Name  : constant W_Name_Id := To_Name (WNE_Rec_Rep);
      Abstr_Ty : constant W_Type_Id := New_Named_Type (Name => Ty_Name);
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
        New_Pointer_Is_Null_Access (E, +Result);

      Result_Address : constant W_Term_Id :=
        New_Pointer_Address_Access (E, +Result);

      Result_Value : constant W_Term_Id :=
        New_Pointer_Value_Access (E, E, +Result);

      Post_Null : constant W_Expr_Id :=
        New_Not (Domain => EW_Prog, Right => +Result_Null);

      Next_Address : constant W_Identifier_Id := New_Identifier
        (Domain => EW_Prog,
         Name   => "__next_pointer_address",
         Module => E_Module (Etype (E)),
         Typ    => EW_Int_Type);

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
         Right  => Insert_Simple_Conversion (Domain  => EW_Prog,
                                             Expr    => +Init_Ident,
                                             To      => EW_Abstract (Des_Ty)));

      Initialized_Post : constant W_Pred_Id := +New_And_Expr
        (Domain => EW_Prog,
         Left   => New_And_Then_Expr (Left   => +Post_Null,
                                      Right  => +Post_Address,
                                      Domain => EW_Prog),
         Right  => +Post_Value);

      Post_Null_Address : constant W_Pred_Id := +New_And_Then_Expr
        (Domain => EW_Prog,
         Left   => +Post_Null,
         Right  => +Post_Address);

      --  ??? Include_Subtypes => False or Include_Subtypes => True
      --  [R525-018]

      PostDefault : constant W_Pred_Id := Compute_Default_Init
        (Expr             => +Result_Value,
         Ty               => Des_Ty,
         Include_Subtypes => True);

      Uninitialized_Post : constant W_Pred_Id :=
        (if Can_Be_Default_Initialized (Des_Ty)
         then
            +New_And_Then_Expr (Domain => EW_Prog,
                                Left   => +Post_Null_Address,
                                Right  => +PostDefault)

         else
            +Post_Null_Address);

      Uninitialized_Pre : constant W_Expr_Id :=
        New_Not (Domain   => EW_Term,
                 Right    => +New_Identifier
                   (Domain => EW_Prog,
                    Name   => To_String (WNE_Null_Exclusion_Val),
                    Module => E_Module (Etype (E))));

      Address_Effects : constant W_Effects_Id :=
        New_Effects (Writes => (1 => +Next_Address));

   begin

      Emit (File,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Program_Space (New_Uninitialized_Name),
               Binders     => R_No_Init_Binder,
               Return_Type => Abstr_Ty,
               Location    => No_Location,
               Labels      => Name_Id_Sets.Empty_Set,
               Pre         => +Uninitialized_Pre,
               Post        => Uninitialized_Post,
               Effects     => Address_Effects));

      Emit (File,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => New_Initialized_Name,
               Binders     => R_Init_Binder,
               Return_Type => Abstr_Ty,
               Location    => No_Location,
               Labels      => Name_Id_Sets.Empty_Set,
               Post        => Initialized_Post,
               Effects     => Address_Effects));

   end Declare_Allocation_Function;

   ---------------------------------------
   -- Declare_Conversion_Check_Function --
   ---------------------------------------

   procedure Declare_Conversion_Check_Function
     (Section : W_Section_Id;
      E       : Entity_Id;
      Root    : Entity_Id)
   is
      Root_Name    : constant W_Name_Id := To_Why_Type (Root);
      Root_Abstr   : constant W_Type_Id :=
        +New_Named_Type (Name => Root_Name);
      A_Ident      : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Root_Abstr);

      Root_Des_Typ : constant Entity_Id := Directly_Designated_Type (Root);
      E_Des_Typ    : constant Entity_Id := Directly_Designated_Type (E);
      Num_Discr    : constant Natural   := Count_Discriminants (E_Des_Typ);

      P_Access : constant W_Term_Id :=
        New_Pointer_Value_Access (E, E, +A_Ident, Local => True);

      R_Access : constant W_Expr_Id :=
        New_Discriminants_Access (Ada_Node => E,
                                  Domain   => EW_Pred,
                                  Name     => +P_Access,
                                  Ty       => Root_Des_Typ);

      Discr : Node_Id := First_Discriminant (E_Des_Typ);

      Post : constant W_Pred_Id :=
        New_Call (Name => Why_Eq,
                  Typ  => EW_Bool_Type,
                  Args => (+New_Result_Ident (Root_Abstr), +A_Ident));

      R_Binder   : Binder_Array (1 .. Num_Discr + 1);
      Args       : W_Expr_Array (1 .. Num_Discr + 1);
      Check_Pred : W_Pred_Id := True_Pred;
      Count      : Natural := 1;
      Pre_Cond   : W_Pred_Id;

   begin
      R_Binder (Num_Discr + 1) :=
        Binder_Type'(B_Name => A_Ident,
                     others => <>);
      Args (Num_Discr + 1) := +A_Ident;
      Count := 1;

      loop
         Args (Count) := +To_Why_Id
           (Discr, Local => True, Rec   => Root,
            Typ          => Base_Why_Type (Etype (Discr)));
         R_Binder (Count) :=
           Binder_Type'
             (B_Name => +Args (Count),
              others => <>);
         Check_Pred :=
           +New_And_Expr
           (Domain => EW_Pred,
            Left   => +Check_Pred,
            Right  =>
              New_Call
                (Domain => EW_Pred,
                 Name   => Why_Eq,
                 Typ    => EW_Bool_Type,
                 Args   =>
                   (1 => +Args (Count),
                    2 =>
                      Insert_Simple_Conversion
                        (Domain   => EW_Term,
                         Expr     => New_Call
                           (Ada_Node => Root,
                            Name     => To_Why_Id
                              (Discr, Rec => Directly_Designated_Type (Root)),
                            Args     => (1 => R_Access),
                            Domain   => EW_Term,
                            Typ      => EW_Abstract (Etype (Discr))),
                         To       => Base_Why_Type (Etype (Discr))))));
         Count := Count + 1;
         Next_Discriminant (Discr);
         exit when No (Discr);
      end loop;

      --  type L (N : Integer) is record
      --    T : Tab (1..N);
      --  end record;
      --  type L_Ptr is access L;
      --  subtype SL_Ptr1 is L_Ptr(42);
      --
      --  ??? The problem here is that the Itype related to L_Ptr(42) is not
      --  translated (E_Pribate_Subtype; [R525-018]). Therefore, no
      --  default_Initial_Assumption is built and the constraint 42 is not
      --  taken into account. This makes the check always return False.

      Emit (Section,
            New_Function_Decl
              (Domain   => EW_Pred,
               Name     => To_Local (E_Symb (E, WNE_Range_Pred)),
               Location => Safe_First_Sloc (E),
               Labels   => Name_Id_Sets.Empty_Set,
               Binders  => R_Binder,
               Def      => +Check_Pred));
      Pre_Cond :=
        New_Call (Name => To_Local (E_Symb (E, WNE_Range_Pred)),
                  Args => Args);
      Emit (Section,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Local (E_Symb (E, WNE_Range_Check_Fun)),
               Binders     => R_Binder,
               Location    => Safe_First_Sloc (E),
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Root_Abstr,
               Pre         => Pre_Cond,
               Post        => Post));
   end Declare_Conversion_Check_Function;

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

      procedure Declare_Access_Function;
      --  Generate the predicate related to the access to a pointer value
      --  (cannot access a null pointer).

      ---------------------
      -- Local Variables --
      ---------------------

      Root      : constant Entity_Id  := Root_Record_Type (E);
      Is_Root   : constant Boolean    := Root = E;
      Ty_Name   : constant W_Name_Id  := To_Name (WNE_Rec_Rep);
      Abstr_Ty  : constant W_Type_Id  := New_Named_Type (Name => Ty_Name);

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      A_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      ------------------------------
      -- Declare_Access_Functions --
      ------------------------------

      procedure Declare_Access_Function is

         Null_Access_Name  : constant String := To_String (WNE_Rec_Comp_Prefix)
         & (Full_Name (E)) & To_String (WNE_Pointer_Value) & "__pred";

         --  The null exclusion defined here is related to the designated type
         --  (that gives the subtype_indication).
         --  This is because the __new_uninitialized_allocator_ is defined
         --  with regard to the the access_type_definition while the
         --  null_exclusion is checked for the subtype_indication.
         --
         --  type Typ is [null_exclusion] access [subtype_indication]
         --  X : Typ := new [subtype_indication]

         Null_Exclusion_Value : constant EW_Literal :=
           (if Can_Never_Be_Null (Directly_Designated_Type (E))
            then
               EW_True
            else
               EW_False);

         Ty         : constant Entity_Id := Etype (E);
         Condition  : W_Pred_Id          := True_Pred;
         Top_Field  : constant W_Expr_Id := +New_Pointer_Is_Null_Access
           (E, +To_Local (E_Symb (Ty, WNE_Null_Pointer)), Local => True);

         Axiom_Name : constant String :=
           To_String (WNE_Null_Pointer) & "__" & Def_Axiom;

      begin
         Emit (P,
               New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => +New_Identifier (Name => Null_Access_Name),
                  Binders  => A_Binder,
                  Location => No_Location,
                  Labels   => Name_Id_Sets.Empty_Set,
                  Def      => New_Not (Domain => EW_Term,
                                       Right  => +New_Pointer_Is_Null_Access
                                         (E, +A_Ident, Local => True))));

         Emit (P,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => +To_Local (E_Symb (Ty, WNE_Null_Pointer)),
                  Binders     => (1 .. 0 => <>),
                  Location    => No_Location,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => Abstr_Ty));

         Emit (P,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => New_Identifier
                    (Name => To_String (WNE_Null_Exclusion_Val)),
                  Binders     => (1 .. 0 => <>),
                  Location    => No_Location,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Bool_Type,
                  Def         => New_Literal (Domain => EW_Term,
                                          Value  => Null_Exclusion_Value)
                 ));

         Condition := +New_Comparison
           (Symbol => Why_Eq,
            Domain => EW_Term,
            Left   => Top_Field,
            Right  => New_Literal (Domain => EW_Term, Value => EW_True));

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
                            (E, E, +A_Ident, Local => True)));

            Precond : constant W_Pred_Id :=
              New_Call
                (Name => New_Identifier (Name => Null_Access_Name),
                 Args => (1 => +A_Ident));

         begin
            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => To_Program_Space
                       (To_Local (E_Symb (E, WNE_Pointer_Value))),
                     Binders     => A_Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => EW_Abstract (Directly_Designated_Type (E)),
                     Pre         => Precond,
                     Post        => Post));

         end;
      end Declare_Access_Function;

      --------------------------
      -- Declare_Pointer_Type --
      --------------------------

      procedure Declare_Pointer_Type is
         Binders_F : Binder_Array (1 .. 3);
         Ty_Name   : constant W_Name_Id := To_Name (WNE_Rec_Rep);

      begin
         if Has_Private_Type (E) then
            --  ??? handle this case
            null;

         else
            Binders_F (1) :=
              (B_Name => To_Local (E_Symb (E, WNE_Is_Null_Pointer)),
               others => <>);

            Binders_F (2) :=
              (B_Name => To_Local (E_Symb (E, WNE_Pointer_Address)),
               others => <>);

            Binders_F (3) :=
              (B_Name => To_Local (E_Symb (E, WNE_Pointer_Value)),
               others => <>);

            Emit_Record_Declaration (Section => P,
                                     Name => Ty_Name,
                                     Binders  => Binders_F,
                                     SPARK_Record => True);

            Emit_Ref_Type_Definition
              (File => P,
               Name => Ty_Name);

            Emit (P, New_Havoc_Declaration (Ty_Name));

            --  Counter for abstract pointer addresses as global variable
            --  ??? should be incremented
            Emit (P,
                  New_Global_Ref_Declaration
                    (Name     => +New_Identifier
                       (Name => "__next_pointer_address"),
                     Labels   => Name_Id_Sets.Empty_Set,
                     Ref_Type => EW_Int_Type,
                     Location => No_Location));
         end if;
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
            Left   => +New_Pointer_Value_Access
              (E, E, +A_Ident, Local => True),
            Right  => +New_Pointer_Value_Access (E, E, +B_Ident, Local => True)
           );

      begin
         --  Compare Pointer_Address field and assume pointer value equality if
         --  addresses are equal.

         Sec_Condition := New_Conditional
           (Domain    => EW_Term,
            Condition => New_Not (Domain => EW_Term,
                                  Right  => +New_Pointer_Is_Null_Access
                                    (E, +A_Ident, Local => True)),
            Then_Part => +New_And_Expr (Left   => +Comparison_Address,
                                        Right  => +Comparison_Value,
                                        Domain => EW_Term));

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_Bool_Eq)),
               Binders     => A_Binder &
                 Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                 others => <>)),
               Return_Type => +EW_Bool_Type,
               Location    => No_Location,
               Labels      => Name_Id_Sets.Empty_Set,
               Def         =>
                 (if Has_Private_Type (E) then Why_Empty
                  else +New_And_Expr
                    (+Comparison_Null, +Sec_Condition, EW_Pred))));

         --  ??? Def empty if private access type?

         --  Declare the dispatching equality function in root types

         if Is_Root and then Is_Tagged_Type (E) then
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Dispatch_Eq)),
                  Return_Type => EW_Bool_Type,
                  Location    => No_Location,
                  Binders     => A_Binder &
                    Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                    others => <>)),
                  Labels      => Name_Id_Sets.Empty_Set));
         end if;
      end Declare_Equality_Function;

   --  Start of processing for Declare_Rep_Pointer_Type

   begin
      Declare_Pointer_Type;
      Declare_Access_Function;

      Emit
        (P,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => To_Local (E_Symb (E, WNE_To_Base)),
            Binders     => A_Binder,
            Labels      => Name_Id_Sets.Empty_Set,
            Location    => No_Location,
            Return_Type => Abstr_Ty,
            Def         => +A_Ident));
      Emit
        (P,
         New_Function_Decl
           (Domain      => EW_Term,
            Name        => To_Local (E_Symb (E, WNE_Of_Base)),
            Binders     => A_Binder,
            Labels      => Name_Id_Sets.Empty_Set,
            Location    => No_Location,
            Return_Type => Abstr_Ty,
            Def         => +A_Ident));

      Declare_Equality_Function;

   end Declare_Rep_Pointer_Type;

   -----------------------------------------
   -- Create_Rep_Pointer_Theory_If_Needed --
   -----------------------------------------

   procedure Create_Rep_Pointer_Theory_If_Needed
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Ancestor : constant Entity_Id := Root_Pointer_Type (E);

   begin
      if Ancestor /= E then
         return;
      end if;

      Pointer_Typ_To_Root.Insert (Directly_Designated_Type (E), E);

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

   ----------------------------
   -- Get_Rep_Pointer_Module --
   ----------------------------

   function Get_Rep_Pointer_Module (E : Entity_Id) return W_Module_Id is
      Ancestor : constant Entity_Id := Root_Pointer_Type (E);
      Name     : constant String    :=
        Full_Name (Ancestor) & To_String (WNE_Rec_Rep);

   begin
      return New_Module (File => No_Name,
                         Name => NID (Name));
   end Get_Rep_Pointer_Module;

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
        E_Symb (Ty, WNE_Pointer_Value);

      Update_Expr : constant W_Expr_Id :=
             New_Record_Update
               (Ada_Node => Ada_Node,
                Name     => Tmp,
                Updates  =>
                  (1 => New_Field_Association
                     (Domain => Domain,
                      Field  => Selected_Field,
                      Value  => Value)),
                Typ      => Get_Type (Name));

   begin
      T := +Sequence
        (+New_Ignore
           (Ada_Node => Ada_Node,
            Prog     => +New_Pointer_Value_Access (Ada_Node => Ada_Node,
                                                   E        => Ty,
                                                   Name     => Tmp,
                                                   Domain   => Domain)),
         +Update_Expr);

      return Binding_For_Temp (Ada_Node, Domain, Tmp, T);
   end New_Ada_Pointer_Update;

   --------------------------------
   -- New_Pointer_Address_Access --
   --------------------------------

   function New_Pointer_Address_Access
     (E     : Entity_Id;
      Name  : W_Expr_Id;
      Local : Boolean := False)
      return W_Term_Id
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
      return W_Term_Id
   is
      Field : constant W_Identifier_Id :=
        (if Local
         then To_Local (E_Symb (E, WNE_Is_Null_Pointer))
         else E_Symb (E, WNE_Is_Null_Pointer));

   begin
      return New_Record_Access (Name   => +Name,
                                Field  => Field,
                                Typ    => EW_Bool_Type);
   end New_Pointer_Is_Null_Access;

   ------------------------------
   -- New_Pointer_Value_Access --
   ------------------------------

   function New_Pointer_Value_Access
     (Ada_Node : Node_Id;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Local    : Boolean := False;
      Domain   : EW_Domain := EW_Term)
      return W_Term_Id
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
            Name     => Field,
            Progs    => (1 => +Name),
            Domain   => EW_Prog,
            Reason   => VC_Null_Pointer_Dereference,
            Typ      => EW_Abstract (Directly_Designated_Type (E)));
      else
         return New_Record_Access (Name  => +Name,
                                   Field => Field,
                                   Typ   => EW_Abstract
                                     (Directly_Designated_Type (E)));
      end if;
   end New_Pointer_Value_Access;

   -----------------------
   -- Root_Pointer_Type --
   -----------------------

   function Root_Pointer_Type (E : Entity_Id) return Entity_Id is
      use Pointer_Typ_To_Roots;

      C : constant Pointer_Typ_To_Roots.Cursor :=
        Pointer_Typ_To_Root.Find (Directly_Designated_Type (Etype (E)));

   begin
      if Has_Element (C) then
         return Pointer_Typ_To_Root (C);
      else
         return E;
      end if;
   end Root_Pointer_Type;

end Why.Gen.Pointers;
