------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - P O I N T E R S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2018-2024, AdaCore                     --
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

with Ada.Containers;              use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Common_Containers;           use Common_Containers;
with GNAT.Source_Info;
with GNATCOLL.Symbols;            use GNATCOLL.Symbols;
with Namet;                       use Namet;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with VC_Kinds;                    use VC_Kinds;
with Why.Atree.Accessors;         use Why.Atree.Accessors;
with Why.Atree.Builders;          use Why.Atree.Builders;
with Why.Atree.Modules;           use Why.Atree.Modules;
with Why.Gen.Arrays;              use Why.Gen.Arrays;
with Why.Gen.Decl;                use Why.Gen.Decl;
with Why.Gen.Expr;                use Why.Gen.Expr;
with Why.Gen.Init;                use Why.Gen.Init;
with Why.Gen.Names;               use Why.Gen.Names;
with Why.Gen.Progs;               use Why.Gen.Progs;
with Why.Gen.Records;             use Why.Gen.Records;
with Why.Gen.Terms;               use Why.Gen.Terms;
with Why.Images;                  use Why.Images;
with Why.Inter;                   use Why.Inter;
with Why.Types;                   use Why.Types;

package body Why.Gen.Pointers is

   procedure Declare_Rep_Pointer_Type
     (Th           : Theory_UC;
      E            : Entity_Id;
      Relaxed_Init : Boolean := False)
   with Pre => Is_Access_Type (E);
   --  Similar to Declare_Rep_Record_Type but for pointer types.

   procedure Complete_Rep_Pointer_Type
     (Th           : Theory_UC;
      E            : Entity_Id;
      Separated    : Boolean;
      Relaxed_Init : Boolean := False)
   with Pre => Is_Access_Type (E);
   --  Declares everything for a representative access type but the type and
   --  predefined equality. If Separated is True then conversion functions
   --  are already declared in another module and we only generate axioms for
   --  them here.

   procedure Declare_Rep_Pointer_Compl
     (E            : Entity_Id;
      Relaxed_Init : Boolean := False)
   with Pre => Is_Access_Type (E);
   --  Declare a new module for completion of access types designating
   --  incomplete types.

   procedure Create_Rep_Pointer_Theory
     (E            : Entity_Id;
      Relaxed_Init : Boolean := False)
   with Pre => Is_Access_Type (E);
   --  Declare a pointer type as a why record with two or three fields:
   --  pointer_value, is_null_pointer, and attr_init if Relaxed_Init is True.
   --  It also defines the needed functions to manipulate this type.

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
      Borrowed_Entity : Entity_Id;
      Borrowed_Expr   : Node_Id;
      Borrowed_Ty     : Entity_Id;
      Borrowed_At_End : W_Identifier_Id;
      Brower_At_End   : W_Identifier_Id;
   end record;
   --  We store for each borrower,
   --   * the root borrowed object in Borrowed_Entity,
   --   * the initially borrowed expression in Borrowed_Expr,
   --   * the enforced type of the borrowed expression in Borrowed_Ty. It is
   --     the type of the first borrow in the expression. It might not be the
   --     type of Borrowed_Expr (usually Borrowed_Expr has a named type while
   --     Borrowed_Ty is an anonymous type) but they are compatible.
   --   * the name of the constant storing the borrowed expression at the end
   --     of the borrow in Borrowed_At_End. It has type Borrowed_Ty.
   --   * the name of the reference holding the value of the borrower at the
   --     end of the borrow in Brower_At_End.

   package Borrow_Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Borrow_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Borrow_Infos : Borrow_Info_Maps.Map;
   --  Maps borrowers to their borrowed object and their pledge

   -----------------------------------------------------
   -- Complete_Move_Tree_For_Incomplete_Access --
   -----------------------------------------------------

   procedure Complete_Move_Tree_For_Incomplete_Access
     (Th : Theory_UC;
      E  : Entity_Id)
   is
      Typ             : constant W_Type_Id :=
        (if Has_Init_Wrapper (E)
         then EW_Init_Wrapper (Type_Of_Node (E))
         else Type_Of_Node (E));
      Obj_Binder      : constant Binder_Type :=
        (B_Name => New_Identifier (Name => "obj", Typ  => Typ),
         others => <>);
      Concrete_Binder : constant Binder_Type :=
        (B_Name => New_Identifier
           (Name => "x",
            Typ  => New_Named_Type (To_Name (WNE_Move_Tree))),
         others => <>);
      Abstract_Binder : constant Binder_Type :=
        (B_Name => New_Identifier
           (Name   => "x",
            Typ    => New_Named_Type
              (Name => New_Name
                   (Symb   => NID (To_String (WNE_Move_Tree)),
                    Module => E_Module (E, Incomp_Move_Tree)))),
         others => <>);

   begin
      --  Generate:
      --
      --  function __open (x : Incompl.move_tree) return move_tree
      --
      --  val __close (x : move_tree) : Incompl.move_tree
      --    ensures { __open result = x }
      --
      --  axiom __is_moved_or_reclaimed_def:
      --    forall x : Incompl.move_tree, obj : <E>.
      --      Incompl.__is_moved_or_reclaimed x obj <->
      --      __is_moved_or_reclaimed (__open x) obj

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (E_Symb (E, WNE_Move_Tree_Open)),
            Binders     => Binder_Array'(1 => Abstract_Binder),
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => Get_Typ (Concrete_Binder.B_Name)));
      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Prog,
            Name        => To_Local (E_Symb (E, WNE_Move_Tree_Close)),
            Binders     => Binder_Array'(1 => Concrete_Binder),
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => Get_Typ (Abstract_Binder.B_Name),
            Post        => New_Comparison
              (Symbol => Why_Eq,
               Left   => +Concrete_Binder.B_Name,
               Right  => New_Call
                 (Name => To_Local (E_Symb (E, WNE_Move_Tree_Open)),
                  Args =>
                    (1 => +New_Result_Ident
                         (Typ => Get_Typ (Abstract_Binder.B_Name)))))));
      Emit (Th,
            New_Defining_Bool_Axiom
              (Name     => New_Identifier
                 (Symb   =>
                      NID (To_String (WNE_Is_Moved_Or_Reclaimed)),
                  Module => E_Module (E, Incomp_Move_Tree),
                  Domain => EW_Pred),
               Fun_Name => To_String (WNE_Is_Moved_Or_Reclaimed),
               Binders  => (1 => Abstract_Binder, 2 => Obj_Binder),
               Def      => New_Call
                 (Name => To_Local (E_Symb (E, WNE_Is_Moved_Or_Reclaimed)),
                  Args => (1 => New_Call
                           (Name   => To_Local
                            (E_Symb (E, WNE_Move_Tree_Open)),
                            Args   => (1 => +Abstract_Binder.B_Name),
                            Domain => EW_Term),
                           2 => +Obj_Binder.B_Name)),
               Dep_Kind => EW_Axdep_Pred));
   end Complete_Move_Tree_For_Incomplete_Access;

   -------------------------------
   -- Complete_Rep_Pointer_Type --
   -------------------------------

   procedure Complete_Rep_Pointer_Type
     (Th           : Theory_UC;
      E            : Entity_Id;
      Separated    : Boolean;
      Relaxed_Init : Boolean := False)
   is

      procedure Declare_Conversion_Check_Function;
      --  Generate a range predicate and a range check function for E

      procedure Declare_Conversion_Functions (As_Axioms : Boolean);
      --  Generate conversion functions from this type to the root type, and
      --  back. If As_Axioms is True, the conversions are already declared in
      --  another module, only emit defining axioms.

      procedure Declare_Access_Function;
      --  Generate the predicate related to the access to a pointer value
      --  (cannot access a null pointer).

      procedure Declare_Wrapper_Conversions (As_Axioms : Boolean) with
        Pre => Relaxed_Init;
      --  Declare conversion functions to and from the wrapper type

      ---------------------
      -- Local Variables --
      ---------------------

      Root     : constant Entity_Id := Root_Pointer_Type (E);
      Is_Root  : constant Boolean   := Root = E;
      Ty_Name  : constant W_Name_Id := To_Name (WNE_Rec_Rep);
      Abstr_Ty : constant W_Type_Id := New_Named_Type
        (Name => Ty_Name, Relaxed_Init => Relaxed_Init);

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
         Value_Id         : constant W_Identifier_Id := To_Local
           (E_Symb (E, WNE_Pointer_Value, Relaxed_Init));

         --  The null exclusion defined here is related to the designated type
         --  (that gives the subtype_indication).
         --  This is because the __new_uninitialized_allocator_ is defined
         --  with regard to the access_type_definition while the
         --  null_exclusion is checked for the subtype_indication.
         --
         --  type Typ is [null_exclusion] access [subtype_indication]
         --  X : Typ := new [subtype_indication]

         Ty        : constant Entity_Id := Etype (E);

         Assign_Pointer : constant W_Identifier_Id :=
           To_Local (E_Symb (E, WNE_Assign_Null_Check, Relaxed_Init));

      begin
         --  If the designated type is incomplete, declare a function to access
         --  the designated value. Otherwise, the record field is enough.

         if Designates_Incomplete_Type (E) then
            Emit (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => Value_Id,
                     Binders     => A_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Get_Typ (Value_Id),
                     Def         => New_Call
                       (Domain => EW_Term,
                        Name   =>
                          To_Local (E_Symb (E, WNE_Open, Relaxed_Init)),
                        Args   =>
                          (1   => New_Record_Access
                               (Name  => +A_Ident,
                                Field => To_Local
                                  (E_Symb
                                     (E            => E,
                                      S            => WNE_Pointer_Value_Abstr,
                                      Relaxed_Init => Relaxed_Init)),
                                Typ   =>
                                  New_Named_Type
                                    (Name => To_Local
                                       (E_Symb
                                     (E            => E,
                                      S            => WNE_Private_Type,
                                      Relaxed_Init => Relaxed_Init))))),
                        Typ    => Get_Typ (Value_Id))));
         end if;

         Emit (Th,
               New_Function_Decl
                 (Domain   => EW_Pred,
                  Name     => +New_Identifier (Name => Null_Access_Name),
                  Binders  => A_Binder,
                  Location => No_Location,
                  Labels   => Symbol_Sets.Empty_Set,
                  Def      => New_Not (Domain => EW_Term,
                                       Right  => New_Pointer_Is_Null_Access
                                         (E, +A_Ident, Local => True))));

         --  N_Null can never have Relaxed_Initialization, no need to declare
         --  a null pointer in the wrapper theory.

         if not Relaxed_Init then
            declare
               Null_Ptr   : constant W_Identifier_Id :=
                 To_Local (E_Symb (Ty, WNE_Null_Pointer));
               Top_Field  : constant W_Expr_Id := New_Pointer_Is_Null_Access
                 (E, +Null_Ptr, Local => True);
               Condition  : constant W_Pred_Id          := New_Call
                 (Name => Why_Eq,
                  Args => (1 => +Top_Field, 2 => +True_Term),
                  Typ  => EW_Bool_Type);
               Axiom_Name : constant String :=
                 To_String (WNE_Null_Pointer) & "__" & Def_Axiom;
            begin
               Emit (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Pterm,
                        Name        => Null_Ptr,
                        Binders     => (1 .. 0 => <>),
                        Location    => No_Location,
                        Labels      => Symbol_Sets.Empty_Set,
                        Return_Type => Abstr_Ty));

               Emit (Th,
                     New_Axiom
                       (Ada_Node => E,
                        Name     => NID (Axiom_Name),
                        Def      => Condition,
                        Dep      =>
                          New_Axiom_Dep (
                            Name => Null_Ptr,
                            Kind => EW_Axdep_Func)));
            end;
         end if;

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
            Emit (Th,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => To_Program_Space (Value_Id),
                     Binders     => A_Binder,
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => No_Location,
                     Return_Type => Get_Typ (Value_Id),
                     Pre         => Precond,
                     Post        => Post));

            Emit (Th,
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

      ---------------------------------------
      -- Declare_Conversion_Check_Function --
      ---------------------------------------

      procedure Declare_Conversion_Check_Function is
         Root_Name  : constant W_Name_Id := To_Why_Type
           (Root, Relaxed_Init => Relaxed_Init);
         Root_Abstr : constant W_Type_Id :=
           +New_Named_Type (Name => Root_Name, Relaxed_Init => Relaxed_Init);
         Des_Ty     : constant Entity_Id :=
           Retysp (Directly_Designated_Type (E));

         R_Ident    : constant W_Identifier_Id :=
           New_Identifier (Name => "r", Typ => Root_Abstr);
         R_Val      : constant W_Term_Id :=
           New_Pointer_Value_Access
             (E    => Root,
              Name => +R_Ident);
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
              New_Bounds_Equality
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
                (Name => E_Symb (Root_Retysp (Des_Ty), WNE_Range_Pred),
                 Args => Args (1 .. Num) & New_Discriminants_Access
                   (Name   => +R_Val,
                    Ty     => Retysp (Directly_Designated_Type (Root))),
                 Typ  => EW_Bool_Type);
         end if;

         --  Do subtype check only if the pointer is not null

         Check_Pred :=
           New_Conditional
             (Condition => New_Not
                (Right  =>
                   Pred_Of_Boolean_Term
                   (New_Pointer_Is_Null_Access
                        (E     => Root,
                         Name  => +R_Ident))),
              Then_Part => Check_Pred,
              Typ       => EW_Bool_Type);

         Emit (Th,
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
         Emit (Th,
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

      procedure Declare_Conversion_Functions (As_Axioms : Boolean) is
         R_Ident   : constant W_Identifier_Id :=
           New_Identifier
             (Name => "r",
              Typ  => EW_Abstract (Root, Relaxed_Init));
         R_Binder  : constant Binder_Array :=
           (1 => (B_Name => R_Ident,
                  others => <>));

      begin
         declare
            Root_Ty : constant W_Type_Id := EW_Abstract (Root, Relaxed_Init);
            Des_Ty  : constant Entity_Id := Directly_Designated_Type (Root);
            Def     : constant W_Term_Id :=
              Pointer_From_Split_Form
                (A            =>
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
                           (Des_Ty,
                            Relaxed_Init =>
                              (if Relaxed_Init then Has_Init_Wrapper (Des_Ty)
                               else Has_Relaxed_Init (Des_Ty))),
                       Force_No_Slide => True),
                    2 => New_Pointer_Is_Null_Access
                      (E     => E,
                       Name  => +A_Ident,
                       Local => True))
                 & (if Relaxed_Init
                    then (1 => New_Record_Access
                          (Name   => +A_Ident,
                           Field  => To_Local (E_Symb (E, WNE_Attr_Init)),
                           Typ    => EW_Bool_Type))
                    else (1 .. 0 => <>)),
                 Ty           => Root,
                 Relaxed_Init => Relaxed_Init);
            --  (value   = to_root a.value,
            --   addr    = a.addr,
            --   is_null = a.is_null)

         begin
            if As_Axioms then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Name     => To_Local
                         (E_Symb (E, WNE_To_Base, Relaxed_Init)),
                     Binders  => A_Binder,
                     Def      => Def));
            else
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local
                       (E_Symb (E, WNE_To_Base, Relaxed_Init)),
                     Binders     => A_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Root_Ty,
                     Def         => +Def));
            end if;
         end;

         declare
            Des_Ty  : constant Entity_Id := Directly_Designated_Type (E);
            Def     : constant W_Term_Id :=
              Pointer_From_Split_Form
                (A            =>
                   (1 => Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => New_Pointer_Value_Access
                         (Ada_Node       => Empty,
                          E              => Root,
                          Name           => +R_Ident,
                          Domain         => EW_Term),
                       To             =>
                         EW_Abstract (Des_Ty,
                           Relaxed_Init =>
                             (if Relaxed_Init then Has_Init_Wrapper (Des_Ty)
                              else Has_Relaxed_Init (Des_Ty))),
                       Force_No_Slide => True),
                    2 => New_Pointer_Is_Null_Access
                      (E     => Root,
                       Name  => +R_Ident))
                 & (if Relaxed_Init
                    then (1 => New_Record_Access
                          (Name   => +R_Ident,
                           Field  => E_Symb (Root, WNE_Attr_Init),
                           Typ    => EW_Bool_Type))
                    else (1 .. 0 => <>)),
                 Ty           => E,
                 Local        => True,
                 Relaxed_Init => Relaxed_Init);
            --  (value   = to_e r.value,
            --   addr    = r.addr,
            --   is_null = r.is_null)

         begin
            if As_Axioms then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Name     => To_Local
                         (E_Symb (E, WNE_Of_Base, Relaxed_Init)),
                     Binders  => R_Binder,
                     Def      => Def));
            else
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local
                       (E_Symb (E, WNE_Of_Base, Relaxed_Init)),
                     Binders     => R_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Abstr_Ty,
                     Def         => +Def));
            end if;
         end;
      end Declare_Conversion_Functions;

      ---------------------------------
      -- Declare_Wrapper_Conversions --
      ---------------------------------

      procedure Declare_Wrapper_Conversions (As_Axioms : Boolean) is
         X_Ident  : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ  => EW_Abstract (E));
         X_Binder : constant Binder_Array :=
           (1 => (B_Name => X_Ident,
                  others => <>));
         Des_Ty   : constant Entity_Id := Directly_Designated_Type (E);

      begin
         declare
            Def : constant W_Term_Id :=
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
                           (Des_Ty, Relaxed_Init => Has_Relaxed_Init (Des_Ty)),
                       Force_No_Slide => True),
                    2 => New_Pointer_Is_Null_Access
                      (E     => E,
                       Name  => +A_Ident,
                       Local => True)),
                 Ty => E);
            --  (value   = of_wrapper a.value,
            --   addr    = a.addr,
            --   is_null = a.is_null)

         begin
            if As_Axioms then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Name     => To_Local (E_Symb (E, WNE_Of_Wrapper)),
                     Binders  => A_Binder,
                     Def      => Def));
            else
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_Of_Wrapper)),
                     Binders     => A_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Get_Typ (X_Ident),
                     Def         => +Def));
            end if;
         end;

         declare
            Def : constant W_Term_Id :=
              Pointer_From_Split_Form
                (A            =>
                   (1 => Insert_Simple_Conversion
                      (Domain         => EW_Term,
                       Expr           => New_Pointer_Value_Access
                         (Ada_Node       => Empty,
                          E              => E,
                          Name           => +X_Ident,
                          Domain         => EW_Term),
                       To             =>
                         EW_Abstract
                           (Des_Ty, Relaxed_Init => Has_Init_Wrapper (Des_Ty)),
                       Force_No_Slide => True),
                    2 => New_Pointer_Is_Null_Access
                      (E     => E,
                       Name  => +X_Ident),
                    3 => +True_Term),
                 Ty           => E,
                 Local        => True,
                 Relaxed_Init => True);
            --  (value       = to_wrapper r.value,
            --   addr        = r.addr,
            --   is_null     = r.is_null,
            --   __attr_init = true)

         begin
            if As_Axioms then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Name     => To_Local
                         (E_Symb (E, WNE_To_Wrapper)),
                     Binders  => X_Binder,
                     Def      => Def));
            else
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_To_Wrapper)),
                     Binders     => X_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Get_Typ (A_Ident),
                     Def         => +Def));
            end if;
         end;
      end Declare_Wrapper_Conversions;

   --  Start of processing for Complete_Rep_Pointer_Type

   begin
      Declare_Access_Function;

      if not Is_Root then
         Declare_Conversion_Functions (As_Axioms => Separated);
         Declare_Conversion_Check_Function;
      else

         --  Declare dummy conversion functions that will be used to convert
         --  other types which use E as a representative type.

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Base, Relaxed_Init)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Of_Base, Relaxed_Init)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
      end if;

      if Relaxed_Init then
         Declare_Wrapper_Conversions (As_Axioms => Separated);
      end if;
   end Complete_Rep_Pointer_Type;

   ---------------------------------------------------
   -- Create_Move_Tree_Theory_For_Incomplete_Access --
   ---------------------------------------------------

   procedure Create_Move_Tree_For_Incomplete_Access (E : Entity_Id) is
      Ty_Name    : constant W_Name_Id := To_Name (WNE_Move_Tree);
      Tree_Ident : constant W_Identifier_Id :=
        New_Identifier
          (Name => "tree",
           Typ  => New_Named_Type (Name => Ty_Name));
      Typ        : constant W_Type_Id :=
        (if Has_Init_Wrapper (E)
         then EW_Init_Wrapper (Type_Of_Node (E))
         else Type_Of_Node (E));
      Obj_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "obj", Typ  => Typ);
      Th         : Theory_UC;

   begin
      Th := Open_Theory
        (WF_Context, E_Module (E, Incomp_Move_Tree),
         Comment =>
           "Module for the abstract move tree for the type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (Th, New_Type_Decl (To_String (WNE_Move_Tree)));

      Emit
        (Th,
         New_Function_Decl
           (Domain   => EW_Pred,
            Name     => To_Local (E_Symb (E, WNE_Is_Moved_Or_Reclaimed)),
            Binders  => Binder_Array'
              (1 => (B_Name => Tree_Ident,
                     others => <>),
               2 => (B_Name => Obj_Ident,
                     others => <>)),
            Location => No_Location,
            Labels   => Symbol_Sets.Empty_Set));

      Close_Theory (Th, Kind => Definition_Theory);
   end Create_Move_Tree_For_Incomplete_Access;

   -----------------------------------------
   -- Create_Move_Tree_Theory_For_Pointer --
   -----------------------------------------

   procedure Create_Move_Tree_Theory_For_Pointer
     (Th : Theory_UC;
      E  : Entity_Id)
   is
      Ty_Name    : constant W_Name_Id := To_Name (WNE_Move_Tree);
      Tree_Ident : constant W_Identifier_Id :=
        New_Identifier
          (Name => "tree",
           Typ  => New_Named_Type (Name => Ty_Name));
      Typ        : constant W_Type_Id :=
        (if Has_Init_Wrapper (E)
         then EW_Init_Wrapper (Type_Of_Node (E))
         else Type_Of_Node (E));
      Obj_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "obj", Typ  => Typ);
      Des_Ty     : constant Entity_Id := Directly_Designated_Type (E);
      Def        : W_Pred_Id;

   begin
      --  For general access types, the pointer itself does not need to be
      --  reclaimed. Rename the move tree of the designated type.

      if Is_General_Access_Type (E) then
         declare
            Des_Module : constant W_Module_Id :=
              (if Designates_Incomplete_Type (E)
               then E_Module (Des_Ty, Incomp_Move_Tree)
               else E_Module (Des_Ty, Move_Tree));
            --  For incomplete designated types, use early declarations

         begin
            Emit (Th,
                  New_Type_Decl
                    (Name  => Ty_Name,
                     Alias => New_Named_Type
                       (Name => New_Name
                            (Symb   => NID (To_String (WNE_Move_Tree)),
                             Module => Des_Module))));

            --  In __is_moved_or_reclaimed, check reclamation of the designated
            --  value if any.

            Def := New_Or_Pred
              (Left  => Pred_Of_Boolean_Term
                 (New_Pointer_Is_Null_Access
                      (Name => +Obj_Ident,
                       E    => E)),
               Right => New_Call
                 (Name => New_Identifier
                      (Symb   => NID (To_String (WNE_Is_Moved_Or_Reclaimed)),
                       Module => Des_Module,
                       Domain => EW_Pred),
                  Args =>
                    (1 => +Tree_Ident,
                     2 => New_Pointer_Value_Access
                       (E => E, Name => +Obj_Ident, Domain => EW_Term))));
         end;

      --  If E is a pool-specific access-to-variable type, introduce toplevel
      --  boolean flag. Flags for the designated values are only necessary if
      --  the designated type is deep.

      else
         declare
            Value_Field_Opt : constant Binder_Array :=
              (if Contains_Allocated_Parts (Des_Ty)
               then
                 (1 => (B_Name =>
                            To_Local (E_Symb (E, WNE_Move_Tree_Ptr_Value)),
                        others => <>))
               else (1 .. 0 => <>));

         begin
            Emit_Record_Declaration
              (Th      => Th,
               Name    => Ty_Name,
               Binders => Binder_Array'
                 (Binder_Type'
                      (B_Name => To_Local
                           (E_Symb (E, WNE_Move_Tree_Ptr_Is_Moved)),
                       others => <>)
                  & Value_Field_Opt));
         end;

         --  In __is_moved_or_reclaimed predicate, check the is_moved flag and
         --  the reclamation on the type.

         Def := New_Or_Pred
           (Left  => Pred_Of_Boolean_Term
              (New_Record_Access
                   (Name  => +Tree_Ident,
                    Field => To_Local (E_Symb (E, WNE_Move_Tree_Ptr_Is_Moved)),
                    Typ   => EW_Bool_Type)),
            Right => Pred_Of_Boolean_Term
              (New_Pointer_Is_Null_Access (Name => +Obj_Ident, E => E)));
      end if;

      Emit_Ref_Type_Definition (Th   => Th,
                                Name => Ty_Name);

      --  Create __is_moved_or_reclaimed predicate

      Emit
        (Th,
         New_Function_Decl
           (Domain   => EW_Pred,
            Name     => To_Local (E_Symb (E, WNE_Is_Moved_Or_Reclaimed)),
            Binders  => Binder_Array'
              (1 => (B_Name => Tree_Ident,
                     others => <>),
               2 => (B_Name => Obj_Ident,
                     others => <>)),
            Location => No_Location,
            Labels   => Symbol_Sets.Empty_Set,
            Def      => +Def));
   end Create_Move_Tree_Theory_For_Pointer;

   -------------------------------
   -- Create_Rep_Pointer_Theory --
   -------------------------------

   procedure Create_Rep_Pointer_Theory
     (E            : Entity_Id;
      Relaxed_Init : Boolean := False)
   is
      Th : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context, E_Module
             (E,
              (if Relaxed_Init then Init_Wrapper_Pointer_Rep
               else Type_Representative)),
           Comment =>
             "Module for axiomatizing the pointer theory associated to type "
           & """" & Get_Name_String (Chars (E)) & """"
           & (if Sloc (E) > 0 then
                " defined at " & Build_Location_String (Sloc (E))
             else "")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Declare_Rep_Pointer_Type (Th, E, Relaxed_Init);

      Close_Theory (Th, Kind => Definition_Theory);
   end Create_Rep_Pointer_Theory;

   -----------------------------------------
   -- Create_Rep_Pointer_Theory_If_Needed --
   -----------------------------------------

   procedure Create_Rep_Pointer_Theory_If_Needed (E : Entity_Id) is
      Ancestor : constant Entity_Id := Repr_Pointer_Type (E);
   begin
      if Ancestor /= Empty then
         return;
      end if;

      Pointer_Typ_To_Root.Insert (Retysp (Directly_Designated_Type (E)), E);

      Create_Rep_Pointer_Theory (E);

      if Has_Init_Wrapper (E) then
         Create_Rep_Pointer_Theory (E, Relaxed_Init => True);
      end if;
   end Create_Rep_Pointer_Theory_If_Needed;

   -------------------------
   -- Declare_Ada_Pointer --
   -------------------------

   procedure Declare_Ada_Pointer (Th : Theory_UC; E : Entity_Id) is
      Rep_Module : constant W_Module_Id := E_Module
        (Repr_Pointer_Type (E), Type_Representative);

   begin
      --  Export the theory containing the pointer record definition.

      Add_With_Clause (Th, Rep_Module, EW_Export);

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
   end Declare_Ada_Pointer;

   -----------------------------
   -- Declare_At_End_Function --
   -----------------------------

   procedure Declare_At_End_Function
     (File    : Theory_UC;
      E       : Entity_Id;
      Binders : Binder_Array)
   is
      Borrowed_Entity : constant Entity_Id := First_Formal (E);
      Current_Module  : constant W_Module_Id := E_Module (E);
      Ty              : constant Entity_Id :=
        Retysp (Etype (Borrowed_Entity));
      Borrowed_Id     : constant W_Identifier_Id :=
        New_Identifier (Symb   => NID (Short_Name (E) & "__borrowed_at_end"),
                        Typ    => Type_Of_Node (Ty),
                        Module => Current_Module,
                        Domain => EW_Prog);
      Brower_Id       : constant W_Identifier_Id :=
        New_Identifier (Symb   => NID (Short_Name (E) & "__result_at_end"),
                        Typ    => Type_Of_Node (Etype (E)),
                        Domain => EW_Prog);

   begin
      --  Emit a declaration for a function computing the value of the borrowed
      --  parameter at the end of the borrow from the call parameters (Binders)
      --  and the value of the result at the end of the borrow.

      Emit (File,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (Borrowed_Id),
               Binders     => Binders &
                 Binder_Type'(B_Name => Brower_Id,
                              B_Ent  => Null_Entity_Name,
                              Labels => Symbol_Sets.Empty_Set,
                              others => <>),
               Return_Type => Get_Typ (Borrowed_Id),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location));

      --  Update the Borrow_Infos map. Also insert a local name for the
      --  borrower at end. It will be used when generating VCs for the
      --  subprogram.

      Borrow_Infos.Insert
        (E, Borrow_Info'(Borrowed_Entity => Borrowed_Entity,
                         Borrowed_Expr   => Borrowed_Entity,
                         Borrowed_Ty     => Ty,
                         Borrowed_At_End => Borrowed_Id,
                         Brower_At_End   => Brower_Id));
   end Declare_At_End_Function;

   ------------------------
   -- Declare_At_End_Ref --
   ------------------------

   procedure Declare_At_End_Ref (Th : Theory_UC; E : Entity_Id) is
      Borrowed_Expr   : Node_Id;
      Borrowed_Ty     : Entity_Id := Etype (E);
      Borrowed_Entity : Entity_Id;

   begin
      --  Find the borrowed initial expression and type.
      --  We go over the initial expression to find the biggest prefix
      --  containing no function calls and we store it in Borrowed_Expr.
      --  Borrowed_Ty is the type of the object borrowing the expression at
      --  this point (either E or the first formal of a call to a traversal
      --  function).

      Get_Observed_Or_Borrowed_Info
        (Expression (Enclosing_Declaration (E)), Borrowed_Expr, Borrowed_Ty);

      --  In case of an access attribute, the borrowed expression is the
      --  prefix.

      if Nkind (Borrowed_Expr) = N_Attribute_Reference
        and then Attribute_Name (Borrowed_Expr) = Name_Access
      then
         Borrowed_Expr := Prefix (Borrowed_Expr);
         Borrowed_Ty   := Etype (Borrowed_Expr);
      end if;

      --  For constant borrowers, the whole object can be considered to be
      --  borrowed as it really is a part of the borrowed parameter of a
      --  traversal function.

      if Is_Constant_Borrower (E) then
         loop
            case Nkind (Borrowed_Expr) is
               when N_Expanded_Name
                  | N_Identifier
               =>
                  Borrowed_Ty := Etype (Borrowed_Expr);
                  exit;

               when N_Explicit_Dereference
                  | N_Indexed_Component
                  | N_Selected_Component
                  | N_Slice
                  | N_Attribute_Reference
               =>
                  Borrowed_Expr := Prefix (Borrowed_Expr);

               when N_Qualified_Expression
                  | N_Type_Conversion
                  | N_Unchecked_Type_Conversion
               =>
                  Borrowed_Expr := Expression (Borrowed_Expr);

               when others =>
                  raise Program_Error;
            end case;
         end loop;
      end if;

      Borrowed_Entity := Get_Root_Object (Borrowed_Expr);

      declare
         Relaxed_Init   : constant Boolean := Obj_Has_Relaxed_Init (E);
         Current_Module : constant W_Module_Id := E_Module (E);
         Brower_Typ     : constant W_Type_Id := Type_Of_Node (Etype (E));
         Brower_Id      : constant W_Identifier_Id :=
           New_Identifier (Symb   => NID (Short_Name (E) & "__brower_at_end"),
                           Typ    =>
                             (if Relaxed_Init then EW_Init_Wrapper (Brower_Typ)
                              else Brower_Typ),
                           Module => Current_Module,
                           Domain => EW_Prog);
         Borrowed_Typ   : constant W_Type_Id := Type_Of_Node (Borrowed_Ty);
         Borrowed_Id    : constant W_Identifier_Id := New_Identifier
           (Symb   => NID (Short_Name (E) & "__borrowed_at_end"),
            Typ    =>
              (if Relaxed_Init then EW_Init_Wrapper (Borrowed_Typ)
               else Borrowed_Typ),
            Module => Current_Module,
            Domain => EW_Prog);
         --  Use the borrowed type for the borrowed at end, since the
         --  invariants of the specific type of the borrowed expression might
         --  be broken during the borrow.

      begin
         --  Declare a global reference for the value of the borrower at the
         --  end of the borrow. We need a reference as this value can be
         --  modified on reborrows.

         Emit (Th,
               New_Global_Ref_Declaration (Name     => To_Local (Brower_Id),
                                           Ref_Type => Get_Typ (Brower_Id),
                                           Labels   => Symbol_Sets.Empty_Set,
                                           Location => No_Location));

         --  Declare a global constant for the value of the borrowed expression
         --  at the end of the borrow. We assume its value on the borrow based
         --  on the value of the borrower at the end.

         Emit (Th,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (Borrowed_Id),
                  Binders     => (1 .. 0 => <>),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => Get_Typ (Borrowed_Id)));

         --  Store information in the Borrow_Infos map

         Borrow_Infos.Insert
           (E, Borrow_Info'(Borrowed_Entity => Borrowed_Entity,
                            Borrowed_Expr   => Borrowed_Expr,
                            Borrowed_Ty     => Borrowed_Ty,
                            Borrowed_At_End => Borrowed_Id,
                            Brower_At_End   => Brower_Id));
      end;
   end Declare_At_End_Ref;

   --------------------------------------
   -- Declare_Init_Wrapper_For_Pointer --
   --------------------------------------

   procedure Declare_Init_Wrapper_For_Pointer
     (Th : Theory_UC;
      E  : Entity_Id)
   is
      Rep_Module : constant W_Module_Id :=
        E_Module (Repr_Pointer_Type (E), Init_Wrapper_Pointer_Rep);

   begin
      --  Export the theory containing the pointer record definition

      Add_With_Clause (Th, Rep_Module, EW_Export);

      --  Rename the representative record type as expected

      Emit (Th, New_Type_Decl
            (Name  => To_Why_Type (E, Local => True, Relaxed_Init => True),
             Alias => +New_Named_Type
               (Name => To_Name (WNE_Rec_Rep))));

   end Declare_Init_Wrapper_For_Pointer;

   -------------------------------
   -- Declare_Rep_Pointer_Compl --
   -------------------------------

   procedure Declare_Rep_Pointer_Compl
     (E            : Entity_Id;
      Relaxed_Init : Boolean := False)
   is
      Des_Ty : constant Entity_Id := Directly_Designated_Type (E);
      Th     : Theory_UC;
   begin
      Th := Open_Theory
        (WF_Context,
         E_Module
           (E,
            (if Relaxed_Init then Init_Wrapper_Completion
             else Type_Completion)),
         Comment =>
           "Module for completing the pointer theory associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_With_Clause
        (Th,
         E_Module
           (Repr_Pointer_Type (E),
            (if Relaxed_Init then Init_Wrapper_Pointer_Rep
             else Type_Representative)),
         EW_Import);

      Emit (Th,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               As_Name       => No_Symbol,
               Origin        => Incomp_Ty_Conv,
               Substitutions =>
                 (1 => New_Clone_Substitution
                      (Kind      => EW_Type_Subst,
                       Orig_Name => New_Name
                         (Symb => NID ("abstr_ty")),
                       Image     => To_Local
                         (Get_Name (E_Symb (E, WNE_Private_Type)))),
                  2 => New_Clone_Substitution
                    (Kind      => EW_Type_Subst,
                     Orig_Name => New_Name
                       (Symb => NID ("comp_ty")),
                     Image     => Get_Name
                       (EW_Abstract
                            (Des_Ty,
                             (if Relaxed_Init then Has_Init_Wrapper (Des_Ty)
                              else Has_Relaxed_Init (Des_Ty))))))));

      Complete_Rep_Pointer_Type
        (Th, E, Separated => True, Relaxed_Init => Relaxed_Init);

      Close_Theory (Th, Kind => Definition_Theory);
   end Declare_Rep_Pointer_Compl;

   -----------------------------------------
   -- Declare_Rep_Pointer_Compl_If_Needed --
   -----------------------------------------

   procedure Declare_Rep_Pointer_Compl_If_Needed (E : Entity_Id) is
      Inserted : Boolean;
      Position : Node_Sets.Cursor;
   begin
      --  Use the Completed_Types set to make sure that we do not complete the
      --  same type twice.

      Completed_Types.Insert (E, Position, Inserted);

      if Inserted then
         Declare_Rep_Pointer_Compl (E);

         if Has_Init_Wrapper (E) then
            Declare_Rep_Pointer_Compl (E, Relaxed_Init => True);
         end if;

      end if;
   end Declare_Rep_Pointer_Compl_If_Needed;

   ------------------------------
   -- Declare_Rep_Pointer_Type --
   ------------------------------

   procedure Declare_Rep_Pointer_Type
     (Th           : Theory_UC;
      E            : Entity_Id;
      Relaxed_Init : Boolean := False)
   is

      procedure Declare_Equality_Function;
      --  Generate the boolean equality function for the pointer type.
      --  As pointer addresses are not represented in SPARK, this equality
      --  function should only be used when one of the operand is statically
      --  null.

      procedure Declare_Pointer_Type;
      --  Emit the why record declaration related to the Ada pointer type

      ---------------------
      -- Local Variables --
      ---------------------

      Ty_Name   : constant W_Name_Id  := To_Name (WNE_Rec_Rep);
      Abstr_Ty  : constant W_Type_Id  := New_Named_Type
        (Name => Ty_Name, Relaxed_Init => Relaxed_Init);
      Value_Id  : constant W_Identifier_Id :=
        (if Designates_Incomplete_Type (E)
         then W_Identifier_Id'(New_Identifier
           (Symb =>
              Get_Symb
                (Get_Name (E_Symb (E, WNE_Pointer_Value_Abstr, Relaxed_Init))),
            Domain => EW_Term,
            Typ    =>
              New_Named_Type
                (To_Local
                   (Get_Name (E_Symb (E, WNE_Private_Type))),
                 Relaxed_Init)))
         else To_Local (E_Symb (E, WNE_Pointer_Value, Relaxed_Init)));

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      A_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      --------------------------
      -- Declare_Pointer_Type --
      --------------------------

      procedure Declare_Pointer_Type is
         Binders_F : Binder_Array (1 .. (if Relaxed_Init then 3 else 2));
         Ty_Name   : constant W_Name_Id := To_Name (WNE_Rec_Rep);

      begin
         pragma Assert (not Has_Incomplete_Or_Private_Type (E));
         Binders_F (1) :=
           (B_Name => To_Local (E_Symb (E, WNE_Is_Null_Pointer)),
            Labels => Get_Model_Trace_Label ("'" & Is_Null_Label),
            others => <>);

         Binders_F (2) :=
           (B_Name => Value_Id,
            Labels => Get_Model_Trace_Label ("'" & All_Label),
            others => <>);

         if Relaxed_Init then
            Binders_F (3) :=
              (B_Name => To_Local (E_Symb (E, WNE_Attr_Init)),
               Labels => Get_Model_Trace_Label ("'" & Initialized_Label),
               others => <>);
         end if;

         Emit_Record_Declaration (Th           => Th,
                                  Name         => Ty_Name,
                                  Binders      => Binders_F,
                                  SPARK_Record => True);

         Emit_Ref_Type_Definition
           (Th   => Th,
            Name => Ty_Name);

         Emit (Th, New_Havoc_Declaration (Ty_Name));
      end Declare_Pointer_Type;

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function is
         B_Ident           : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);

         Sec_Condition     : W_Pred_Id;

         Comparison_Null   : constant W_Pred_Id :=
           New_Comparison
           (Symbol => Why_Eq,
            Left   => New_Pointer_Is_Null_Access (E, +A_Ident, Local => True),
            Right  => New_Pointer_Is_Null_Access (E, +B_Ident, Local => True));

         Comparison_Value : constant W_Pred_Id :=
           New_Comparison
           (Symbol => Why_Eq,
            Left   => New_Record_Access
              (Name  => +A_Ident,
               Field => Value_Id,
               Typ   => Get_Typ (Value_Id)),
            Right  => New_Record_Access
              (Name  => +B_Ident,
               Field => Value_Id,
               Typ   => Get_Typ (Value_Id)));

      begin
         --  Compare Pointer_Null field and the pointer value if any. The
         --  second part should never be used.

         Sec_Condition := New_Conditional
           (Condition => New_Not (Right  => Pred_Of_Boolean_Term
                                  (New_Pointer_Is_Null_Access
                                       (E, +A_Ident, Local => True))),
            Then_Part => Comparison_Value);

         Emit
           (Th,
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
                 +New_And_Pred (Comparison_Null, Sec_Condition)));
      end Declare_Equality_Function;

   --  Start of processing for Declare_Rep_Pointer_Type

   begin
      --  For types designating incomplete types, declare a new uninterpreted
      --  type for the value component.

      if Designates_Incomplete_Type (E) then
         Emit (Th,
               New_Type_Decl
                 (Name => Img
                    (Get_Symb (To_Local (E_Symb (E, WNE_Private_Type)))))
              );
      end if;

      Declare_Pointer_Type;
      Declare_Equality_Function;

      if not Designates_Incomplete_Type (E) then
         Complete_Rep_Pointer_Type
           (Th, E, Separated => False, Relaxed_Init => Relaxed_Init);

      --  Declare the conversion functions to and from the root type as well as
      --  to and from the initialization wrapper if any. These declarations
      --  will be completed in the completion module.

      else
         if Root_Pointer_Type (E) /= E then
            declare
               Root      : constant Entity_Id := Root_Pointer_Type (E);
               Root_Ty   : constant W_Type_Id := EW_Abstract
                 (Root, Relaxed_Init);
               R_Ident   : constant W_Identifier_Id :=
                 New_Identifier (Name => "r", Typ => Root_Ty);
               R_Binder  : constant Binder_Array :=
                 (1 => (B_Name => R_Ident,
                        others => <>));

            begin
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_To_Base)),
                     Binders     => A_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Root_Ty));
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_Of_Base)),
                     Binders     => R_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Abstr_Ty));
            end;
         end if;

         if Relaxed_Init then
            declare
               X_Ident  : constant W_Identifier_Id :=
                 New_Identifier
                   (Name => "x",
                    Typ  =>
                      EW_Abstract (E, Relaxed_Init => Has_Relaxed_Init (E)));
               X_Binder : constant Binder_Array :=
                 (1 => (B_Name => X_Ident,
                        others => <>));

            begin
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_Of_Wrapper)),
                     Binders     => A_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Get_Typ (X_Ident)));
               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_To_Wrapper)),
                     Binders     => X_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => Get_Typ (A_Ident)));
            end;
         end if;
      end if;
   end Declare_Rep_Pointer_Type;

   -------------------------
   -- Get_Borrowed_At_End --
   -------------------------

   function Get_Borrowed_At_End (E : Entity_Id) return W_Identifier_Id is
     (Borrow_Infos (E).Borrowed_At_End);

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

   -----------------------
   -- Get_Brower_At_End --
   -----------------------

   function Get_Brower_At_End (E : Entity_Id) return W_Identifier_Id is
     (Borrow_Infos (E).Brower_At_End);

   ------------------------------------
   -- Has_Predeclared_Init_Predicate --
   ------------------------------------

   function Has_Predeclared_Init_Predicate (E : Entity_Id) return Boolean is
     (Has_Incomplete_Access (E)
      and then Has_Init_Wrapper (Retysp (Get_Incomplete_Access (E))));

   ----------------------------------
   -- Insert_Pointer_Subtype_Check --
   ----------------------------------

   function Insert_Pointer_Subtype_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id
   is
      Relaxed_Init : constant Boolean := Get_Relaxed_Init (Get_Type (+Expr));
      Root         : constant Entity_Id := Root_Pointer_Type (Check_Ty);
      Des_Ty       : constant Entity_Id :=
        Retysp (Directly_Designated_Type (Retysp (Check_Ty)));
      Ptr_Expr     : W_Prog_Id := Expr;

   begin
      if not Is_Constrained (Des_Ty) or else Is_Constrained (Root) then
         return Expr;
      else
         --  Insert a check that the address of Expr is initialized

         Ptr_Expr := +Insert_Top_Level_Init_Check
           (Ada_Node => Ada_Node,
            E        => Get_Ada_Node (+Get_Type (+Expr)),
            Name     => +Ptr_Expr,
            Domain   => EW_Prog);

         return New_VC_Call
           (Ada_Node => Ada_Node,
            Name     => E_Symb (Check_Ty, WNE_Range_Check_Fun, Relaxed_Init),
            Progs    =>
              Prepare_Args_For_Access_Subtype_Check
                (Check_Ty, +Ptr_Expr, EW_Pterm, Body_Params),
            Reason   => (if Has_Array_Type (Des_Ty) then VC_Range_Check
                         else VC_Discriminant_Check),
            Typ      => Get_Type (+Ptr_Expr));
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

      Relaxed_Init   : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed

      Selected_Field : constant W_Identifier_Id :=
        (if Designates_Incomplete_Type (Repr_Pointer_Type (Ty))
         then E_Symb (Ty, WNE_Pointer_Value_Abstr, Relaxed_Init)
         else E_Symb (Ty, WNE_Pointer_Value, Relaxed_Init));

      --  If Ty designates an incomplete type, we need to reconstruct the
      --  abstract value.

      Rec_Val     : constant W_Expr_Id :=
        (if Designates_Incomplete_Type (Repr_Pointer_Type (Ty))
         then New_Call
           (Domain => Domain,
            Name   => E_Symb (Ty, WNE_Close, Relaxed_Init),
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

   --------------------------------
   -- New_Pointer_Is_Null_Access --
   --------------------------------

   function New_Pointer_Is_Null_Access
     (E     : Entity_Id;
      Name  : W_Expr_Id;
      Local : Boolean := False)
      return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed

      Field        : W_Identifier_Id :=
        E_Symb (E, WNE_Is_Null_Pointer, Relaxed_Init);

   begin
      if Local then
         Field := To_Local (Field);
      end if;

      return New_Record_Access (Name  => +Name,
                                Field => Field,
                                Typ   => EW_Bool_Type);
   end New_Pointer_Is_Null_Access;

   ----------------------------------------
   -- New_Move_Tree_Pointer_Value_Access --
   ----------------------------------------

   function New_Move_Tree_Pointer_Value_Access
     (Ty     : Entity_Id;
      Name   : W_Expr_Id;
      Domain : EW_Domain)
      return W_Expr_Id
   is
      Des_Ty : constant Entity_Id := Directly_Designated_Type (Ty);
      Value  : W_Expr_Id := Name;

   begin
      --  Values of an anonymous access type cannot be moved themselves. Their
      --  move tree is directly the move tree of the designated value.

      if Is_Anonymous_Access_Type (Ty) then
         return Name;
      end if;

      if not Is_General_Access_Type (Ty) then
         declare
            Field : constant W_Identifier_Id :=
              E_Symb (Ty, WNE_Move_Tree_Ptr_Value);
         begin
            Value := New_Record_Access
              (Name  => Value,
               Field => Field,
               Typ   => Get_Typ (Field));
         end;
      end if;

      if Has_Incomplete_Access (Des_Ty) then
         declare
            Open_Id : constant W_Identifier_Id := E_Symb
              (Des_Ty, WNE_Move_Tree_Open);
         begin
            return New_Call
              (Name   => Open_Id,
               Args   => (1 => Value),
               Typ    => Get_Typ (Open_Id),
               Domain => Domain);
         end;
      else
         return Value;
      end if;
   end New_Move_Tree_Pointer_Value_Access;

   ----------------------------------------
   -- New_Move_Tree_Pointer_Value_Update --
   ----------------------------------------

   function New_Move_Tree_Pointer_Value_Update
     (Ty    : Entity_Id;
      Name  : W_Prog_Id;
      Value : W_Prog_Id)
      return W_Prog_Id
   is
      Des_Ty : constant Entity_Id := Directly_Designated_Type (Ty);
      Val    : W_Prog_Id := Value;

   begin
      --  Values of an anonymous access type cannot be moved themselves. Their
      --  move tree is directly the move tree of the designated value.

      if Is_Anonymous_Access_Type (Ty) then
         return Value;
      end if;

      if Has_Incomplete_Access (Des_Ty) then
         declare
            Close_Id : constant W_Identifier_Id := E_Symb
              (Des_Ty, WNE_Move_Tree_Close);
         begin
            Val := New_Call
              (Name => Close_Id,
               Args => (1 => +Val),
               Typ  => Get_Typ (Close_Id));
         end;
      end if;

      if Is_General_Access_Type (Ty) then
         return Val;
      else
         return New_Record_Update
           (Name  => +Name,
            Updates =>
              (1 => New_Field_Association
                   (Domain => EW_Prog,
                    Field  => E_Symb (Ty, WNE_Move_Tree_Ptr_Value),
                    Value  => +Val)));
      end if;
   end New_Move_Tree_Pointer_Value_Update;

   ------------------------------
   -- New_Pointer_Value_Access --
   ------------------------------

   function New_Pointer_Value_Access
     (Ada_Node : Node_Id := Empty;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain;
      Local    : Boolean := False)
      return W_Expr_Id
   is
      Relaxed_Init : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed

      Field        : W_Identifier_Id :=
        E_Symb (E, WNE_Pointer_Value, Relaxed_Init);

   begin
      if Local then
         Field :=  To_Local (Field);
      end if;

      if Domain = EW_Prog and then not Can_Never_Be_Null (E) then
         return
           +New_VC_Call
           (Ada_Node => Ada_Node,
            Name     => To_Program_Space (Field),
            Progs    => (1 => +Name),
            Reason   => VC_Null_Pointer_Dereference,
            Typ      => Get_Typ (Field));

      elsif Designates_Incomplete_Type (Repr_Pointer_Type (Retysp (E))) then
         return New_Call (Args   => (1 => Name),
                          Name   => Field,
                          Domain => Domain,
                          Typ    => Get_Typ (Field));

      else
         return New_Record_Access (Name  => +Name,
                                   Field => Field,
                                   Typ   => Get_Typ (Field));
      end if;
   end New_Pointer_Value_Access;

   -------------------------------------------
   -- Prepare_Args_For_Access_Subtype_Check --
   -------------------------------------------

   function Prepare_Args_For_Access_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params)
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
                 +Get_Array_Attr (Domain => Term_Domain (Domain),
                                  Ty     => Des_Ty,
                                  Attr   => Attribute_First,
                                  Dim    => Count);
               Args (2 * Count) :=
                 +Get_Array_Attr (Domain => Term_Domain (Domain),
                                  Ty     => Des_Ty,
                                  Attr   => Attribute_Last,
                                  Dim    => Count);
            end loop;
            return Args;
         end;

      --  Get the discriminants of the designated type

      else
         pragma Assert (Has_Discriminants (Des_Ty));
         return Get_Discriminants_Of_Subtype
           (Des_Ty, Term_Domain (Domain), Params) & Expr;
      end if;
   end Prepare_Args_For_Access_Subtype_Check;

   -----------------------------
   -- Pointer_From_Split_Form --
   -----------------------------

   function Pointer_From_Split_Form
     (I           : Item_Type;
      Ref_Allowed : Boolean)
      return W_Term_Id
   is
      Des_Ty       : constant Entity_Id := Directly_Designated_Type (I.P_Typ);
      Relaxed_Init : constant Boolean :=
        I.Init.Present
        or else
          (if Has_Init_Wrapper (I.P_Typ) and then not Has_Relaxed_Init (Des_Ty)
           then Get_Module (Get_Name (Get_Typ (I.Value.B_Name)))
             = E_Module (Des_Ty, Init_Wrapper)
           else False);
      E            : constant Entity_Id := I.Value.Ada_Node;
      Ty           : constant Entity_Id := I.P_Typ;
      Value        : W_Expr_Id;
      Is_Null      : W_Expr_Id;
      Attr_Init    : W_Expr_Array (1 .. (if Relaxed_Init then 1 else 0));

   begin
      if I.Value.Mutable and then Ref_Allowed then
         Value := New_Deref (E, I.Value.B_Name, Get_Typ (I.Value.B_Name));
      else
         Value := +I.Value.B_Name;
      end if;

      if I.Mutable and then Ref_Allowed then
         Is_Null := New_Deref (E, I.Is_Null, Get_Typ (I.Is_Null));
      else
         Is_Null := +I.Is_Null;
      end if;

      if I.Init.Present then
         if Ref_Allowed then
            Attr_Init (1) := New_Deref (E, I.Init.Id, EW_Bool_Type);
         else
            Attr_Init (1) := +I.Init.Id;
         end if;
      elsif Relaxed_Init then
         Attr_Init (1) := +True_Term;
      end if;

      return Pointer_From_Split_Form
        (Ada_Node     => E,
         A            =>
           (1 => Value, 2 => Is_Null) & Attr_Init,
         Ty           => Ty,
         Relaxed_Init => Relaxed_Init);
   end Pointer_From_Split_Form;

   function Pointer_From_Split_Form
     (Ada_Node     : Node_Id := Empty;
      A            : W_Expr_Array;
      Ty           : Entity_Id;
      Local        : Boolean := False;
      Relaxed_Init : Boolean := False)
      return W_Term_Id
   is
      Ty_Ext     : constant Entity_Id := Retysp (Ty);
      Value      : W_Expr_Id := A (1);
      Is_Null    : constant W_Expr_Id := A (2);
      S_Value    : W_Identifier_Id :=
        (if Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext))
         then E_Symb (Ty_Ext, WNE_Pointer_Value_Abstr, Relaxed_Init)
         else E_Symb (Ty_Ext, WNE_Pointer_Value, Relaxed_Init));
      S_Is_Null  : W_Identifier_Id :=
        E_Symb (Ty_Ext, WNE_Is_Null_Pointer, Relaxed_Init);
      W_Ty       : W_Type_Id := EW_Abstract (Ty_Ext, Relaxed_Init);

   begin
      --  If Local use local names for the fields of Ty and for its abstract
      --  type.

      if Local then
         S_Value := To_Local (S_Value);
         S_Is_Null := To_Local (S_Is_Null);
         W_Ty := New_Named_Type
           (New_Name (Symb => Get_Symb (Get_Name (W_Ty))));
      end if;

      --  If Ty designates an incomplete type, we need to reconstruct the
      --  abstract value.

      if Designates_Incomplete_Type (Repr_Pointer_Type (Ty_Ext)) then
         Value := New_Call
           (Domain => EW_Term,
            Name   =>
              (if Local
               then To_Local (E_Symb (Ty_Ext, WNE_Close, Relaxed_Init))
               else E_Symb (Ty_Ext, WNE_Close, Relaxed_Init)),
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
                 Field  => S_Is_Null,
                 Value  => Is_Null))
         & (if Relaxed_Init
            then (1 => New_Field_Association
                  (Domain => EW_Term,
                   Field  =>
                     (if Local
                      then To_Local (E_Symb (Ty_Ext, WNE_Attr_Init))
                      else E_Symb (Ty_Ext, WNE_Attr_Init)),
                   Value  => A (3)))
            else (1 .. 0 => <>)),
         Typ          => W_Ty);
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
         return Standard.Types.Empty;
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
