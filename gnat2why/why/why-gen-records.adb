------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;

with Atree;               use Atree;
with Einfo;               use Einfo;
with Elists;              use Elists;
with Nlists;              use Nlists;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;

with SPARK_Util;          use SPARK_Util;
with VC_Kinds;            use VC_Kinds;

with Common_Containers;   use Common_Containers;

with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Gen.Terms;       use Why.Gen.Terms;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

package body Why.Gen.Records is

   --  For all Ada record types, we define a Why3 record type which contains
   --  all components of the Ada type, including discriminants, and including
   --  components in variant parts.

   --  For all such components, we then declare access program functions, where
   --  the precondition represents the discriminant check, and the
   --  postcondition states that the value of this function is just the value
   --  of the record component.

   --  The precondition for such access discriminant checks is actually
   --  separated out in a separate predicate. This predicate is only generated
   --  for root types, and subtypes of the root type refer to that predicate
   --  for their own access program functions. For a root type, the
   --  declarations may be as follows:

   --    predicate y__check__pred (a : t) = a.x = 1
   --  ( to check that discriminant "x" is set to 1, and this is the check
   --  predicate for record field "y")

   --  In a root type we directly refer to that predicate in the program
   --  function

   --    val rec__y_ (a : t)
   --    requires { y__check__pred (a) }

   --  In a non-root type, we refer to the predicate of the root type, and must
   --  insert a conversion in addition:

   --    val rec__y_ (a : t)
   --    requires { Root_type.y__check__pred ( to_base (a)) }

   --  For all record types which are not root types, we also define conversion
   --  functions to the root type (in logic space) and from the root type (in
   --  logic and program space).

   --  For all record types which are not root types, we define a check
   --  function, which checks whether its argument is in the current
   --  (sub-)type. This check function must be defined over the root type,
   --  otherwise it is not expressible or trivially true. This function is
   --  similar to the range_check functions in scalar/array types. In many
   --  cases, the subtype constraints are dynamic, so we cannot refer to them
   --  directly here. Instead, we take them as additional arguments:

   --  val range_check_ (x : base) (d1 : type_of_discr_1)
   --                              (d2 : type_of_discr_d2)
   --  requires { d1 = constr_of_first_discr /\ d2 = constr_of_second_discr }
   --  ensures  { result = x }

   --  For the implementation details: This is one place where we have to look
   --  at the declaration node to find which discriminant values imply the
   --  presence of which components. We traverse the N_Component_List of the
   --  type declaration, and for each component, and for each N_Variant_Part,
   --  we store a record of type [Component_Info] which contains the N_Variant
   --  node to which the component/variant part belongs, and the N_Variant_Part
   --  to which this N_Variant node belongs. In this way, we can easily access
   --  the discriminant (the Name of the N_Variant_Part) and the discrete
   --  choice (the Discrete_Choices of the N_Variant) of that component or
   --  variant part. For variant parts, the field [Ident] is empty, for
   --  components it contains the corresponding Why identifier.

   --  The map [Comp_Info] maps the component entities and N_Variant_Part nodes
   --  to their information record. This map is populated at the beginning of
   --  [Declare_Ada_Record].

   --  We ignore "completely hidden" components of derived record types (see
   --  also the discussion in einfo.ads and sem_ch3.adb)

   type Component_Info is record
      Parent_Variant  : Node_Id;
      Parent_Var_Part : Node_Id;
      Ident           : W_Identifier_Id;
   end record;

   package Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Component_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   function Is_Not_Hidden_Discriminant (E : Entity_Id) return Boolean is
     (not (Ekind (E) = E_Discriminant and then Is_Completely_Hidden (E)));
   --  Opposite of Einfo.Is_Completely_Hidden, which also returns True if E is
   --  not a discriminant.

   function Count_Why_Record_Fields (E : Entity_Id) return Natural;
   --  count the number of fields

   function Count_Discriminants (E : Entity_Id) return Natural;
   --  count the number of discriminants

   function Discriminant_Check_Pred_Name (E     : Entity_Id;
                                          Field : Entity_Id;
                                          Local : Boolean)
                                          return W_Identifier_Id;
   --  Given a record field, return the name of its discrimant check
   --  predicate. If Local is true, do not prefix the identifier.
   --  If the current record type is not a root type, return the name of the
   --  corresponding predicate in the root type module.

   -------------------------
   -- Count_Discriminants --
   -------------------------

   function Count_Discriminants (E : Entity_Id) return Natural
   is
      Discr : Entity_Id := First_Discriminant (E);
      Count : Natural := 0;
   begin
      while Present (Discr) loop
         if Is_Not_Hidden_Discriminant (Discr) then
            Count := Count + 1;
         end if;
         Next_Discriminant (Discr);
      end loop;
      return Count;
   end Count_Discriminants;

   -----------------------------
   -- Count_Why_Record_Fields --
   -----------------------------

   function Count_Why_Record_Fields (E : Entity_Id) return Natural
   is
      Cnt : Natural := 0;
      Field : Node_Id := First_Component_Or_Discriminant (E);
   begin
      while Present (Field) loop
         if Is_Not_Hidden_Discriminant (Field) then
            Cnt := Cnt + 1;
         end if;
         Next_Component_Or_Discriminant (Field);
      end loop;
      return Cnt;
   end Count_Why_Record_Fields;

   -----------------------
   -- Declare_Ada_Record --
   -----------------------

   procedure Declare_Ada_Record
     (P       : Why_Section;
      Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id)
   is

      procedure Declare_Record_Type;
      --  declare the record type

      procedure Declare_Protected_Access_Functions;
      --  for each record field, declare an access program function, whose
      --  result is the same as the record field access, but there is a
      --  precondition (when needed)

      function Compute_Discriminant_Check (Field : Entity_Id)
                                           return W_Pred_Id;
      --  compute the discriminant check for an access to the given field, as a
      --  predicate which can be used as a precondition

      function Compute_Others_Choice (Info  : Component_Info;
                                      Discr : W_Term_Id) return W_Pred_Id;
      --  compute (part of) the discriminant check for one discriminant in the
      --  special case where the N_Discrete_Choice is actually an
      --  N_Others_Choice

      procedure Declare_Conversion_Functions;
      --  Generate conversion functions from this type to the root type, and
      --  back.

      procedure Declare_Equality_Function;
      --  Generate the boolean equality function for the record type

      function Discriminant_Check_Pred_Call (Field : Entity_Id;
                                             Arg : W_Identifier_Id)
                                             return W_Pred_Id;
      --  Given a record field, return the a call to its discrimant check
      --  predicate, with the given argument. If that predicate is defined
      --  elsewhere (i.e. in the module for the root record type, prefix the
      --  call accordingly and add a conversion.

      function Transform_Discrete_Choices (Case_N : Node_Id;
                                           Expr   : W_Term_Id)
                                           return W_Pred_Id;
      --  Wrapper for the function in Gnat2Why.Expr;

      procedure Init_Component_Info;
      --  Initialize the map which maps each component to its information
      --  record

      Root       : constant Entity_Id := Root_Record_Type (E);
      Is_Root    : constant Boolean := Root = E;
      Ty_Ident   : constant W_Identifier_Id := To_Why_Id (E, Local => True);
      Abstr_Ty   : constant W_Type_Id := New_Named_Type (Name => Ty_Ident);
      Comp_Info  : Info_Maps.Map := Info_Maps.Empty_Map;
      --  This map maps each component and each N_Variant node to a
      --  Component_Info record. This map is initialized by a call to
      --  Init_Component_Info;

      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder   : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      --------------------------------
      -- Compute_Discriminant_Check --
      --------------------------------

      function Compute_Discriminant_Check (Field : Entity_Id)
                                           return W_Pred_Id
      is
         Info : Component_Info := Comp_Info.Element (Field);
         Cond : W_Pred_Id := True_Pred;
      begin
         while Present (Info.Parent_Variant) loop
            declare
               Ada_Discr : constant Node_Id :=
                 Entity (Name (Info.Parent_Var_Part));
               Discr : constant W_Term_Id :=
                 +Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr =>
                      New_Record_Access
                        (Name  => +A_Ident,
                         Field => To_Why_Id (Ada_Discr, Local => True),
                         Typ   => EW_Abstract (Etype (Ada_Discr))),
                    To   => EW_Int_Type);
               New_Cond : constant W_Pred_Id :=
                 (if Is_Others_Choice (Discrete_Choices (Info.Parent_Variant))
                  then
                  Compute_Others_Choice (Info, Discr)
                  else
                  +Transform_Discrete_Choices
                    (Info.Parent_Variant, Discr));
            begin
               Cond :=
                 +New_And_Then_Expr
                 (Domain => EW_Pred,
                  Left   => +Cond,
                  Right  => +New_Cond);
               Info := Comp_Info.Element (Info.Parent_Var_Part);
            end;
         end loop;
         return Cond;
      end Compute_Discriminant_Check;

      ---------------------------
      -- Compute_Others_Choice --
      ---------------------------

      function Compute_Others_Choice (Info  : Component_Info;
                                      Discr : W_Term_Id) return W_Pred_Id
      is
         Var_Part : constant Node_Id := Info.Parent_Var_Part;
         Var      : Node_Id := First (Variants (Var_Part));
         Cond     : W_Pred_Id := True_Pred;
      begin
         while Present (Var) loop
            if not Is_Others_Choice (Discrete_Choices (Var)) then
               Cond :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Cond,
                    Right  =>
                      New_Not
                        (Domain => EW_Pred,
                         Right  =>
                           +Transform_Discrete_Choices (Var, Discr)));
            end if;
            Next (Var);
         end loop;
         return Cond;
      end Compute_Others_Choice;

      ----------------------------------
      -- Declare_Conversion_Functions --
      ----------------------------------

      procedure Declare_Conversion_Functions
      is
         Root            : constant Entity_Id :=
           Unique_Entity (Root_Record_Type (E));
         Num_E_Fields    : constant Natural := Count_Why_Record_Fields (E);
         Num_Root_Fields : constant Natural := Count_Why_Record_Fields (Root);
         To_Root_Aggr    : W_Field_Association_Array (1 .. Num_Root_Fields);
         From_Root_Aggr  : W_Field_Association_Array (1 .. Num_E_Fields);
         Field           : Entity_Id;
         Seen            : Node_Sets.Set := Node_Sets.Empty_Set;
         Index           : Natural := 1;
         A_Ident         : constant W_Identifier_Id :=
           New_Identifier (Name => "a", Typ => EW_Abstract (Root));
         From_Binder     : constant Binder_Array :=
           (1 => (B_Name => A_Ident,
                  others => <>));
         From_Ident     : constant W_Identifier_Id := To_Ident (WNE_Of_Base);

      begin
         pragma Assert (Num_E_Fields <= Num_Root_Fields);

         --  First iterate over the the components of the subtype; this allows
         --  to fill in the 'from' aggregate and part of the 'to' aggregate. We
         --  store in 'Seen' the components of the base type which are already
         --  filled in.

         Field := First_Component_Or_Discriminant (E);
         while Present (Field) loop
            if Is_Not_Hidden_Discriminant (Field) then
               declare
                  Orig     : constant Entity_Id :=
                    Root_Record_Component (Field);
                  Orig_Id  : constant W_Identifier_Id := To_Why_Id (Orig);
                  Field_Id : constant W_Identifier_Id :=
                    To_Why_Id (Field, Local => True);
               begin
                  From_Root_Aggr (Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => Field_Id,
                       Value  =>
                         Insert_Simple_Conversion
                           (Domain => EW_Term,
                            To     => EW_Abstract (Etype (Field)),
                            Expr   =>
                              New_Record_Access
                                (Name => +A_Ident,
                                 Field => Orig_Id,
                                 Typ   => EW_Abstract (Etype (Orig)))));
                  To_Root_Aggr (Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => Orig_Id,
                       Value  =>
                         Insert_Simple_Conversion
                           (Domain => EW_Term,
                            To     => EW_Abstract (Etype (Orig)),
                            Expr   =>
                              New_Record_Access
                                (Name  => +A_Ident,
                                 Field => Field_Id,
                                 Typ   => EW_Abstract (Etype (Field)))));
                  Seen.Include (Orig);
                  Index := Index + 1;
               end;
            end if;
            Next_Component_Or_Discriminant (Field);
         end loop;

         --  We now iterate over the components of the root type, to fill in
         --  the missing part of the 'to' aggregate. As the subtype cannot
         --  provide a value for these fields, we use the dummy value of the
         --  corresponding type. We use the 'Seen' set to filter the components
         --  that have been added already.

         --  ??? For renamed discriminants, we should reuse the value of the
         --  renaming

         Field := First_Component_Or_Discriminant (Root);
         while Present (Field) loop
            if not (Seen.Contains (Field)) then
               To_Root_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => To_Why_Id (Field),
                    Value  =>
                      Why_Default_Value
                        (Domain => EW_Term,
                         E      => Etype (Field)));
               Index := Index + 1;
            end if;
            Next_Component_Or_Discriminant (Field);
         end loop;

         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Ident (WNE_To_Base),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type =>
                 EW_Abstract (Root),
               Def         =>
                 New_Record_Aggregate
                   (Associations => To_Root_Aggr)));
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => From_Ident,
               Binders     => From_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         =>
                 New_Record_Aggregate
                   (Associations => From_Root_Aggr)));
      end Declare_Conversion_Functions;

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function
      is
         B_Ident   : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);
         Condition : W_Pred_Id := True_Pred;
         Comp      : Entity_Id := First_Component_Or_Discriminant (E);
      begin
         while Present (Comp) loop
            if Is_Not_Hidden_Discriminant (Comp) then
               declare
                  Comparison : constant W_Pred_Id :=
                    +New_Ada_Equality
                    (Typ    => Unique_Entity (Etype (Comp)),
                     Domain => EW_Pred,
                     Left   =>
                       New_Record_Access
                         (Name  => +A_Ident,
                          Field => To_Why_Id (Comp, Local => True),
                          Typ   => EW_Abstract (Etype (Comp))),
                     Right  =>
                       New_Record_Access
                         (Name  => +B_Ident,
                          Field => To_Why_Id (Comp, Local => True),
                          Typ   => EW_Abstract (Etype (Comp))),
                     Force_Predefined =>
                        not Is_Record_Type (Etype (Comp)));
                  Always_Present : constant Boolean :=
                    not (Has_Discriminants (E)) or else
                    Ekind (Comp) = E_Discriminant;
               begin
                  Condition :=
                    +New_And_Then_Expr
                    (Domain => EW_Pred,
                     Left   => +Condition,
                     Right  =>
                       (if Always_Present then +Comparison
                        else
                        New_Connection
                          (Domain => EW_Pred,
                           Op     => EW_Imply,
                           Left   =>
                             +Discriminant_Check_Pred_Call (Comp, A_Ident),
                           Right  => +Comparison)));
               end;
            end if;
            Next_Component_Or_Discriminant (Comp);
         end loop;
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Ident (WNE_Bool_Eq),
               Binders     =>
                 R_Binder &
               Binder_Array'(1 =>
                  Binder_Type'(B_Name => B_Ident,
                               others => <>)),
               Return_Type => +EW_Bool_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Def         =>
                 New_Conditional
                   (Domain    => EW_Term,
                    Condition => +Condition,
                    Then_Part => +True_Term,
                    Else_Part => +False_Term)));
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Name => "user_eq"),
               Return_Type => EW_Bool_Type,
               Binders     => R_Binder &
                 Binder_Array'(1                   =>
                                   Binder_Type'(B_Name => B_Ident,
                                                others => <>)),
               Labels      => Name_Id_Sets.Empty_Set));
      end Declare_Equality_Function;

      ----------------------------------------
      -- Declare_Protected_Access_Functions --
      ----------------------------------------

      procedure Declare_Protected_Access_Functions
      is
         Field : Entity_Id := First_Component_Or_Discriminant (E);
      begin

         --  ??? enrich the postcondition of access to discriminant, whenever
         --  we statically know its value (in case of E_Record_Subtype)

         while Present (Field) loop
            if Is_Not_Hidden_Discriminant (Field) then
               declare
                  Pred_Name : constant W_Identifier_Id :=
                    Discriminant_Check_Pred_Name (E, Field, True);
               begin

                  --  For fields of root record types, we generate a
                  --  discriminant check predicate. Unneeded for discriminants,
                  --  whose predicate is always "true.

                  if Is_Root and then Ekind (Field) /= E_Discriminant then
                     declare
                        Pre_Cond  : constant W_Pred_Id :=
                          (if Ekind (Field) = E_Discriminant then True_Pred
                           else Compute_Discriminant_Check (Field));
                     begin
                        Emit (Theory,
                              New_Function_Decl
                                (Domain => EW_Pred,
                                 Name   => Pred_Name,
                                 Binders => R_Binder,
                                 Labels  => Name_Id_Sets.Empty_Set,
                                 Def => +Pre_Cond));
                     end;
                  end if;

                  --  In any case, we generate a program access function, whose
                  --  precondition is precisely the predicate. Note that
                  --  [Precond] has been computed so that it uses the correct
                  --  predicate name, whether it has been defined here or in
                  --  the root type. In the case of a discriminant, the
                  --  precondition is simply "true".

                  declare
                     Why_Name  : constant W_Identifier_Id :=
                       To_Why_Id (Field, Local => True);
                     Prog_Name : constant W_Identifier_Id :=
                       To_Program_Space (Why_Name);
                     Post : constant W_Pred_Id :=
                       New_Relation
                         (Left    => +New_Result_Ident (Why_Empty),
                          Op_Type => EW_Abstract,
                          Op      => EW_Eq,
                          Right   =>
                            New_Record_Access
                              (Name => +A_Ident,
                               Field => Why_Name));
                     Precond     : constant W_Pred_Id :=
                       (if Ekind (Field) = E_Discriminant then True_Pred
                        else Discriminant_Check_Pred_Call (Field, A_Ident));
                  begin
                     Emit (Theory,
                           New_Function_Decl
                             (Domain      => EW_Prog,
                              Name        => Prog_Name,
                              Binders     => R_Binder,
                              Labels  => Name_Id_Sets.Empty_Set,
                              Return_Type =>
                                EW_Abstract (Etype (Field)),
                              Pre         => Precond,
                              Post        => Post));
                  end;
               end;
            end if;
            Next_Component_Or_Discriminant (Field);
         end loop;
      end Declare_Protected_Access_Functions;

      -------------------------
      -- Declare_Record_Type --
      -------------------------

      procedure Declare_Record_Type
      is
         Num_Fields : constant Natural := Count_Why_Record_Fields (E);
         Binders    : Binder_Array (1 .. Num_Fields);
         Field      : Entity_Id := First_Component_Or_Discriminant (E);
      begin
         for Index in 1 .. Num_Fields loop
            Binders (Index) :=
              (B_Name =>
                 To_Why_Id
                   (Field,
                    Local => True,
                    Typ => EW_Abstract (Etype (Field))),
               others => <>);
            loop
               Next_Component_Or_Discriminant (Field);
               exit when not (Present (Field)) or else
                 Is_Not_Hidden_Discriminant (Field);
            end loop;
         end loop;
         Emit (Theory,
           New_Record_Definition (Name    => Ty_Ident,
                                  Binders => Binders));
      end Declare_Record_Type;

      function Discriminant_Check_Pred_Call (Field : Entity_Id;
                                             Arg : W_Identifier_Id)
                                             return W_Pred_Id
      is
         Precond_Arg : constant W_Term_Id :=
           (if Is_Root then +Arg
            else New_Call
              (Name => To_Ident (WNE_To_Base),
               Args => (1 => +Arg)));
      begin
         return
           New_Call
             (Name => Discriminant_Check_Pred_Name (E, Field, True),
              Args => (1 => +Precond_Arg));
      end Discriminant_Check_Pred_Call;

      -------------------------
      -- Init_Component_Info --
      -------------------------

      procedure Init_Component_Info is
         procedure Mark_Component_List (N : Node_Id;
                                        Parent_Var_Part : Node_Id;
                                        Parent_Variant  : Node_Id);

         procedure Mark_Variant_Part (N : Node_Id;
                                      Parent_Var_Part : Node_Id;
                                      Parent_Variant  : Node_Id);

         --------------------------
         -- Mark_Component_Items --
         --------------------------

         procedure Mark_Component_List (N               : Node_Id;
                                        Parent_Var_Part : Node_Id;
                                        Parent_Variant  : Node_Id) is
            Field : Node_Id := First (Component_Items (N));
         begin
            while Present (Field) loop
               if Nkind (Field) /= N_Pragma then
                  Comp_Info.Insert
                    (Defining_Identifier (Field),
                     Component_Info'(
                       Parent_Variant  => Parent_Variant,
                       Parent_Var_Part => Parent_Var_Part,
                       Ident           =>
                         To_Why_Id
                           (Defining_Identifier (Field),
                            Local => True)));
               end if;
               Next (Field);
            end loop;
            if Present (Variant_Part (N)) then
               Mark_Variant_Part (Variant_Part (N),
                                  Parent_Var_Part,
                                  Parent_Variant);
            end if;
         end Mark_Component_List;

         -----------------------
         -- Mark_Variant_Part --
         -----------------------

         procedure Mark_Variant_Part (N               : Node_Id;
                                      Parent_Var_Part : Node_Id;
                                      Parent_Variant  : Node_Id) is
            Var : Node_Id := First (Variants (N));
         begin
            Comp_Info.Insert (N, Component_Info'(
              Parent_Variant  => Parent_Variant,
              Parent_Var_Part => Parent_Var_Part,
              Ident           => Why_Empty));
            while Present (Var) loop
               Mark_Component_List (Component_List (Var), N, Var);
               Next (Var);
            end loop;
         end Mark_Variant_Part;

         Decl_Node  : constant Node_Id := Parent (E);
         Field : Node_Id := First (Discriminant_Specifications (Decl_Node));
         Components : constant Node_Id :=
           Component_List (Type_Definition (Decl_Node));
      begin
         while Present (Field) loop
            Comp_Info.Insert
              (Defining_Identifier (Field),
               Component_Info'
                 (Parent_Variant  => Empty,
                  Parent_Var_Part => Empty,
                  Ident           =>
                    To_Why_Id (Defining_Identifier (Field),
                      Local => True)));
            Next (Field);
         end loop;
         if Present (Components) then
            Mark_Component_List (Components, Empty, Empty);
         end if;
      end Init_Component_Info;

      --------------------------------
      -- Transform_Discrete_Choices --
      --------------------------------

      function Transform_Discrete_Choices (Case_N : Node_Id;
                                           Expr   : W_Term_Id)
                                           return W_Pred_Id
      is
      begin
         return +Gnat2Why.Expr.Transform_Discrete_Choices
           (Choices      => Discrete_Choices (Case_N),
            Choice_Type  => Empty,  --  not used for predicates, can be empty
            Matched_Expr => +Expr,
            Cond_Domain  => EW_Pred,
            Params       => Logic_Params);
      end Transform_Discrete_Choices;

   begin

      --  Get the empty record case out of the way

      if Count_Why_Record_Fields (E) = 0 then
         Emit (Theory,
               New_Type_Decl
                 (Name => Ty_Ident,
                  Labels => Name_Id_Sets.Empty_Set));
         return;
      end if;

      --  ??? We probably still need a way to tell that the right conversion
      --  function from this records subtype should go through the clone.

      if Ekind (E) = E_Record_Subtype and then
        Present (Cloned_Subtype (E))
      then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and generate trivial conversion functions,
         --  then return

         declare
            Clone : constant Entity_Id := Cloned_Subtype (E);
         begin
            Add_Use_For_Entity (P, Clone, EW_Export, With_Completion => False);

            --  if the copy has the same name as the original, do not redefine
            --  the type name.

            if Short_Name (E) /= Short_Name (Clone) then
               Emit (Theory,
                     New_Type_Decl
                       (Name => Ty_Ident,
                        Alias =>
                          +New_Named_Type
                          (Name =>
                               To_Why_Id (Clone, Local => True))));
            end if;

            --  if the cloned type is a root type, we need to define the
            --  conversion functions; in all other cases, they are already
            --  there.

            if Root_Record_Type (Clone) = Clone then
               Emit
                 (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Ident (WNE_To_Base),
                     Binders     => R_Binder,
                     Labels  => Name_Id_Sets.Empty_Set,
                     Return_Type => Abstr_Ty,
                     Def         => +A_Ident));
               Emit
                 (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Ident (WNE_Of_Base),
                     Binders     => R_Binder,
                     Labels  => Name_Id_Sets.Empty_Set,
                     Return_Type => Abstr_Ty,
                     Def         => +A_Ident));
            end if;
         end;
         return;
      end if;
      if Ekind (E) /= E_Record_Subtype then
         Init_Component_Info;
      end if;
      Declare_Record_Type;

      --  We need to delare conversion functions before the protected access
      --  functions, because the former may be used in the latter

      if not Is_Root then
         Declare_Conversion_Functions;
      end if;
      Declare_Protected_Access_Functions;
      Declare_Equality_Function;
      if not Is_Root
        and then Has_Discriminants (E)
        and then Is_Constrained (E)
      then
         Declare_Conversion_Check_Function (Theory, E, Root);
      end if;
   end Declare_Ada_Record;

   ---------------------------------------
   -- Declare_Conversion_Check_Function --
   ---------------------------------------

   procedure Declare_Conversion_Check_Function
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id;
      Root   : Entity_Id)
   is
      Root_Ident : constant W_Identifier_Id := To_Why_Id (Root);
      Root_Abstr : constant W_Type_Id :=
        +New_Named_Type (Name => Root_Ident);
      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Root_Abstr);
      Num_Discr  : constant Natural := Count_Discriminants (E);
      Discr      : Node_Id := First_Discriminant (E);
      Post       : constant W_Pred_Id :=
        New_Relation (Op      => EW_Eq,
                      Op_Type => EW_Abstract,
                      Left    => +New_Result_Ident (Why_Empty),
                      Right   => +A_Ident);
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
      Discr := First_Discriminant (E);
      while Present (Discr) loop
         if Is_Not_Hidden_Discriminant (Discr) then
            R_Binder (Count) :=
              Binder_Type'
                (B_Name =>
                   To_Why_Id
                     (Discr,
                      Local => True,
                      Typ => EW_Abstract (Etype (Discr))),
                 others => <>);
            Args (Count) := +To_Why_Id (Discr, Local => True);
            Check_Pred :=
              +New_And_Expr
              (Domain => EW_Pred,
               Left   => +Check_Pred,
               Right  =>
                 New_Relation
                   (Domain => EW_Pred,
                    Op      => EW_Eq,
                    Op_Type => EW_Abstract,
                    Left    => +To_Why_Id (Discr, Local => True),
                    Right   =>
                      New_Call
                        (Ada_Node => Root,
                         Name     => To_Why_Id (Discr, Rec => Root),
                         Args     => (1 => +A_Ident),
                         Domain   => EW_Term)));
            Count := Count + 1;
         end if;
         Next_Discriminant (Discr);
      end loop;
      Emit (Theory,
            New_Function_Decl
              (Domain      => EW_Pred,
               Name        => To_Ident (WNE_Range_Pred),
               Labels  => Name_Id_Sets.Empty_Set,
               Binders     => R_Binder,
               Def         => +Check_Pred));
      Pre_Cond :=
        New_Call (Name   => To_Ident (WNE_Range_Pred),
                  Args   => Args);
      Emit (Theory,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Ident (WNE_Range_Check_Fun),
               Binders     => R_Binder,
               Labels  => Name_Id_Sets.Empty_Set,
               Return_Type => Root_Abstr,
               Pre         => Pre_Cond,
               Post        => Post));
   end Declare_Conversion_Check_Function;

   ----------------------------------
   -- Discriminant_Check_Pred_Name --
   ----------------------------------

   function Discriminant_Check_Pred_Name (E     : Entity_Id;
                                          Field : Entity_Id;
                                          Local : Boolean)
                                          return W_Identifier_Id
   is
      Root       : constant Entity_Id := Root_Record_Type (E);
      Is_Root    : constant Boolean := Root = E;
      Name   : constant String := Short_Name (Field) & "__pred";
   begin
      if Is_Root then
         if Local then
            return New_Identifier (Name => Name);
         else
            return New_Identifier
              (Domain   => EW_Pred,
               Ada_Node => E,
               Module   => E_Module (E),
               Name     => Name);
         end if;
      else
         return New_Identifier
           (Domain   => EW_Pred,
            Ada_Node => Root,
            Module   => E_Module (Root),
            Name     => Name);
      end if;
   end Discriminant_Check_Pred_Name;

   ---------------------------------------
   -- Insert_Subtype_Discriminant_Check --
   ---------------------------------------

   function Insert_Subtype_Discriminant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
   is
      Root : constant Entity_Id :=
        (if Type_Based_On_External_Axioms (Check_Ty) then
              Underlying_External_Axioms_Type (Check_Ty)
         else Root_Record_Type (Check_Ty));
   begin
      --  We make a last verification here to see whether a discriminant check
      --  is actually necessary.

      --  If the type does not have any discriminants, no check is needed
      --  obviously.

      if not Has_Discriminants (Check_Ty) then
         return Expr;
      end if;

      --  If the check type is a "root type", we cannot generate a check, as
      --  we do not have the appropriate predicate in Why3. However, the
      --  frontend always generates appropriate subtypes for discriminant
      --  records. As a consequence, we can only end up with the "root" type
      --  as a check type if we are in the case of a record type with default
      --  discriminants. But this case does not require checks.

      if Root = Check_Ty then
         return Expr;
      end if;

      --  The check type can still have default discriminants. We check that
      --  explicitly here.

      if not Is_Constrained (Check_Ty) and then
        Present (Discriminant_Constraint (Check_Ty)) and then
        not Is_Empty_Elmt_List (Discriminant_Constraint (Check_Ty))
      then
         return Expr;
      end if;

      return
        +New_VC_Call
        (Ada_Node => Ada_Node,
         Name     => Range_Check_Name (Check_Ty, RCK_Range),
         Progs    => Prepare_Args_For_Subtype_Check (Check_Ty, +Expr),
         Domain   => EW_Prog,
         Reason   => VC_Discriminant_Check,
         Typ      => Get_Type (+Expr));
   end Insert_Subtype_Discriminant_Check;

   ---------------------------
   -- New_Ada_Record_Access --
   ---------------------------

   function New_Ada_Record_Access
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Call_Id : constant W_Identifier_Id := To_Why_Id (Field, Rec => Ty);
      Ret_Ty  : constant W_Type_Id :=
        Type_Of_Node (Search_Component_By_Name (Ty, Field));
   begin
      if Domain = EW_Prog and then
        Do_Discriminant_Check (Ada_Node)
      then
         return
           New_VC_Call
             (Ada_Node => Ada_Node,
              Name     => To_Program_Space (Call_Id),
              Progs    => (1 => Name),
              Domain   => Domain,
              Reason   => VC_Discriminant_Check,
              Typ      => Ret_Ty);
      else
         return
           New_Call
             (Ada_Node => Ada_Node,
              Name     => Call_Id,
              Args     => (1 => Name),
              Domain   => Domain,
              Typ      => Ret_Ty);
      end if;
   end New_Ada_Record_Access;

   ------------------------------------
   -- New_Ada_Record_Check_For_Field --
   ------------------------------------

   function New_Ada_Record_Check_For_Field
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Root : constant Entity_Id := Root_Record_Type (Ty);
   begin
      return
        New_Call
          (Ada_Node => Ada_Node,
           Name     => Discriminant_Check_Pred_Name (Ty, Field, False),
           Args     => (1 => Insert_Simple_Conversion (Ada_Node => Ada_Node,
                                                       Domain   => Domain,
                                                       Expr     => Name,
                                                       To       =>
                                                         EW_Abstract (Root))),
           Domain   => Domain,
           Typ      => EW_Bool_Type);
   end New_Ada_Record_Check_For_Field;

   ---------------------------
   -- New_Ada_Record_Update --
   ---------------------------

   function New_Ada_Record_Update
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Value    : W_Expr_Id)
      return W_Expr_Id
   is
      Tmp         : constant W_Expr_Id := New_Temp_For_Expr (Name);
      Ty          : constant Entity_Id := Get_Ada_Node (+Get_Type (Name));
      Update_Expr : constant W_Expr_Id :=
        New_Record_Update
          (Ada_Node => Ada_Node,
           Name     => Tmp,
           Updates  =>
             (1 =>
                New_Field_Association
                  (Domain => Domain,
                   Field  => To_Why_Id (Field, Domain, Rec => Ty),
                   Value  => Value)),
           Typ      => Get_Type (Name));
      T           : W_Expr_Id;
   begin
      if Domain = EW_Prog then
         T := +Sequence
           (+New_Ignore
              (Ada_Node => Ada_Node,
               Prog     =>
                 +New_Ada_Record_Access
                 (Ada_Node, Domain, Tmp, Field, Ty)),
            +Update_Expr);
      else
         T := Update_Expr;
      end if;
      return Binding_For_Temp (Ada_Node, Domain, Tmp, T);
   end New_Ada_Record_Update;

   ------------------------------------
   -- Prepare_Args_For_Subtype_Check --
   ------------------------------------

   function Prepare_Args_For_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id) return W_Expr_Array
   is
      Num_Discr : constant Natural := Count_Discriminants (Check_Ty);
      Args      : W_Expr_Array (1 .. Num_Discr + 1);
      Count     : Natural := 1;
      Discr     : Entity_Id := First_Discriminant (Check_Ty);
      Elmt      : Elmt_Id := First_Elmt (Stored_Constraint (Check_Ty));
   begin
      Args (Num_Discr + 1) := +Expr;
      while Present (Discr) loop
         if Is_Not_Hidden_Discriminant (Discr) then
            Args (Count) :=
              Transform_Expr
                (Domain => EW_Term,
                 Params => Logic_Params,
                 Expr   => Node (Elmt),
                 Expected_Type => EW_Abstract (Etype (Discr)));
            Count := Count + 1;
            Next_Elmt (Elmt);
         end if;
         Next_Discriminant (Discr);
      end loop;
      return Args;
   end Prepare_Args_For_Subtype_Check;

end Why.Gen.Records;
