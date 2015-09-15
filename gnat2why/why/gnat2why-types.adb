------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Ada.Text_IO;  --  For debugging, to print info before raising an exception
with Atree;               use Atree;
with Common_Containers;   use Common_Containers;
with Einfo;               use Einfo;
with Flow_Types;          use Flow_Types;
with GNAT.Source_Info;
with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Namet;               use Namet;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;
with Sinput;              use Sinput;
with SPARK_Definition;    use SPARK_Definition;
with SPARK_Util;          use SPARK_Util;
with Stand;               use Stand;
with Why;                 use Why;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Arrays;      use Why.Gen.Arrays;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Records;     use Why.Gen.Records;
with Why.Gen.Scalars;     use Why.Gen.Scalars;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

package body Gnat2Why.Types is

   ------------------------------
   -- Generate_Type_Completion --
   ------------------------------

   procedure Generate_Type_Completion
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      procedure Create_Axioms_For_Scalar_Bounds
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Create axioms defining the values of non-static scalar bounds

      procedure Create_Default_Init_Assumption
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Create a function to express type E's default initial assumption

      procedure Create_Dynamic_Invariant
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Create a function to express type E's dynamic invariant

      procedure Create_Dynamic_Predicate
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Create a function to express type E's predicate

      -------------------------------------
      -- Create_Axioms_For_Scalar_Bounds --
      -------------------------------------

      procedure Create_Axioms_For_Scalar_Bounds
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id)
      is
         procedure Create_Axiom_For_Expr
           (Name : W_Identifier_Id;
            Bnd  : Node_Id;
            Typ  : W_Type_Id);
         --  Create a defining axiom for a logic function which can be used
         --  instead of E.

         ---------------------------
         -- Create_Axiom_For_Expr --
         ---------------------------

         procedure Create_Axiom_For_Expr
           (Name : W_Identifier_Id;
            Bnd  : Node_Id;
            Typ  : W_Type_Id)
         is
            Items : Item_Array :=
              Get_Binders_From_Expression (Bnd);
            Def   : W_Term_Id;

         begin
            --  Use local names for variables

            Localize_Variable_Parts (Items);

            --  Push the names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def := +Transform_Expr
              (Expr          => Bnd,
               Expected_Type => Typ,
               Domain        => EW_Term,
               Params        => Logic_Params (File.Kind));

            Emit (Theory,
                  New_Defining_Axiom
                    (Name    => Name,
                     Def     => +Def,
                     Binders => Get_Parameters_From_Binders (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end Create_Axiom_For_Expr;

         Rng       : constant Node_Id := Get_Range (E);

      begin
         if not Is_Static_Expression (Low_Bound (Rng)) then
            Create_Axiom_For_Expr
              (Name => E_Symb (E, WNE_Attr_First),
               Bnd  => Low_Bound (Rng),
               Typ  => Base_Why_Type (E));
         end if;
         if not Is_Static_Expression (High_Bound (Rng)) then
            Create_Axiom_For_Expr
              (Name => E_Symb (E, WNE_Attr_Last),
               Bnd  => High_Bound (Rng),
               Typ  => Base_Why_Type (E));
         end if;
      end Create_Axioms_For_Scalar_Bounds;

      ------------------------------------
      -- Create_Default_Init_Assumption --
      ------------------------------------

      procedure Create_Default_Init_Assumption
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id)
      is
         Variables : Flow_Id_Sets.Set;

      begin

         --  Get the set of variables used in E's default initialization

         Variables_In_Default_Init (E, Variables);

         declare
            Items    : Item_Array :=
              Get_Binders_From_Variables (To_Name_Set (Variables));
            Main_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => Type_Of_Node (E));
            --  Expression on which we want to assume the property

            Slst_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);
            --  Only assume initial condition for the components

            Def : W_Pred_Id;

         begin
            --  Use local names for variables

            Localize_Variable_Parts (Items);

            --  Push the names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def := Compute_Default_Init
              (Expr           => +Main_Arg,
               Ty             => E,
               Skip_Last_Cond => +Slst_Arg,
               Params         => Logic_Params (File.Kind),
               Use_Pred       => False);

            Emit (Theory,
                  New_Function_Decl
                    (Domain  => EW_Pred,
                     Name    => To_Local (E_Symb (E, WNE_Default_Init)),
                     Def     => +Def,
                     Labels  => Name_Id_Sets.To_Set (NID ("inline")),
                     Binders =>
                       Binder_Array'(1 => Binder_Type'(B_Name => Main_Arg,
                                                       others => <>),
                                     2 => Binder_Type'(B_Name => Slst_Arg,
                                                       others => <>))
                     & Get_Parameters_From_Binders (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end Create_Default_Init_Assumption;

      ------------------------------
      -- Create_Dynamic_Invariant --
      ------------------------------

      procedure Create_Dynamic_Invariant
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id)
      is
         Variables : Flow_Id_Sets.Set;

      begin

         --  Get the set of variables used in E's dynamic property

         Variables_In_Dynamic_Invariant (E, Variables);

         declare
            Items    : Item_Array :=
              Get_Binders_From_Variables (To_Name_Set (Variables));
            Init_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);
            --  Is the object known to be initialized

            Ovar_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);
            --  Do we need to assume the properties on constant parts

            Top_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => EW_Bool_Type);
            --  Should we check the toplevel predicate

            Main_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => Type_Of_Node (E));
            --  Expression on which we want to assume the property

            Def : W_Pred_Id;

         begin
            --  Use local names for variables

            Localize_Variable_Parts (Items);

            --  Push the names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def := Compute_Dynamic_Invariant
              (Expr          => +Main_Arg,
               Ty            => E,
               Initialized   => +Init_Arg,
               Only_Var      => +Ovar_Arg,
               Top_Predicate => +Top_Arg,
               Params        => Logic_Params (File.Kind),
               Use_Pred      => False);

            Emit (Theory,
                  New_Function_Decl
                    (Domain  => EW_Pred,
                     Name    => To_Local (E_Symb (E, WNE_Dynamic_Invariant)),
                     Def     => +Def,
                     Labels  => Name_Id_Sets.To_Set (NID ("inline")),
                     Binders =>
                       Binder_Array'(1 => Binder_Type'(B_Name => Main_Arg,
                                                       others => <>),
                                     2 => Binder_Type'(B_Name => Init_Arg,
                                                       others => <>),
                                     3 => Binder_Type'(B_Name => Ovar_Arg,
                                                       others => <>),
                                     4 => Binder_Type'(B_Name => Top_Arg,
                                                       others => <>))
                     & Get_Parameters_From_Binders (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end Create_Dynamic_Invariant;

      ------------------------------
      -- Create_Dynamic_Predicate --
      ------------------------------

      procedure Create_Dynamic_Predicate
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id)
      is
         Variables : Flow_Id_Sets.Set;

      begin
         --  Get the set of variables used in E's predicate

         Variables_In_Dynamic_Predicate (E, Variables);

         declare
            Items    : Item_Array :=
              Get_Binders_From_Variables (To_Name_Set (Variables));
            Main_Arg : constant W_Identifier_Id :=
              New_Temp_Identifier (Typ => Type_Of_Node (E));
            --  Expression on which we want to assume the property
            Def : W_Pred_Id;

         begin
            --  Use local names for variables

            Localize_Variable_Parts (Items);

            --  Push the names to Symbol_Table

            Ada_Ent_To_Why.Push_Scope (Symbol_Table);
            Push_Binders_To_Symbol_Table (Items);

            Def := Compute_Dynamic_Predicate
                     (Expr     => +Main_Arg,
                      Ty       => E,
                      Params   => Logic_Params (File.Kind),
                      Use_Pred => False);

            Emit
              (Theory,
               Why.Gen.Binders.New_Function_Decl
                 (Domain      => EW_Pred,
                  Name        => To_Local (E_Symb (E, WNE_Dynamic_Predicate)),
                  Def         => +Def,
                  Labels  => Name_Id_Sets.To_Set (NID ("inline")),
                  Binders =>
                    Binder_Array'(1 => Binder_Type'(B_Name => Main_Arg,
                                                    others => <>))
                    & Get_Parameters_From_Binders (Items)));

            Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
         end;
      end Create_Dynamic_Predicate;

      Ty        : constant W_Type_Id := EW_Abstract (E);
   begin

      Open_Theory
        (File, E_Axiom_Module (E),
         Comment =>
           "Module giving axioms for type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      declare
         Eq  : Entity_Id := Get_User_Defined_Eq (E);
      begin

         --  This module only contains an axiom when there is a user-provided
         --  equality

         if Present (Eq)
           and then Entity_In_SPARK (Eq)
         then

            --  we may need to adjust for renamed subprograms

            if Present (Renamed_Entity (Eq)) then
               Eq := Renamed_Entity (Eq);
            end if;

            declare
               Need_Convert : constant Boolean :=
                 Is_Scalar_Type (E) and then not Is_Boolean_Type (E);
               Var_A : constant W_Identifier_Id :=
                 New_Identifier (Ada_Node => E,
                                 Name     => "a",
                                 Typ      => Ty);
               Var_B : constant W_Identifier_Id :=
                 New_Identifier (Ada_Node => E,
                                 Name     => "b",
                                 Typ      => Ty);
               Arg_A : constant W_Expr_Id :=
                 (if Need_Convert then
                     Insert_Simple_Conversion
                    (Domain => EW_Term,
                     Expr   => +Var_A,
                     To     => Base_Why_Type (Ty))
                  else +Var_A);
               Arg_B : constant W_Expr_Id :=
                 (if Need_Convert then
                     Insert_Simple_Conversion
                    (Domain => EW_Term,
                     Expr   => +Var_B,
                     To     => Base_Why_Type (Ty))
                  else +Var_B);
               Def   : constant W_Expr_Id :=
                 New_Call
                   (Ada_Node => Eq,
                    Domain   => EW_Pred,
                    Name     => To_Why_Id (E => Eq,
                                           Domain => EW_Pred,
                                           Typ => EW_Bool_Type),
                    Args     => (1 => Arg_A, 2 => Arg_B),
                    Typ      => EW_Bool_Type);
            begin
               Emit
                 (File.Cur_Theory,
                  New_Defining_Axiom
                    (Ada_Node    => E,
                     Binders     =>
                       (1 => Binder_Type'(B_Name => Var_A, others => <>),
                        2 => Binder_Type'(B_Name => Var_B, others => <>)),
                     Name        =>
                       New_Identifier
                         (Module => E_Module (E),
                          Name    => "user_eq"),
                     Def         => +Def));
            end;
         end if;
      end;

      --  Generate a predicate for E's dynamic property. For provability, it is
      --  inlined by Why3.
      --  We do not generate the dynamic property for Itypes as they may
      --  depend on locally defined constants such as 'Old.

      if not Is_Itype (E) then
         Create_Dynamic_Invariant (File.Cur_Theory, E);

         --  Generate a predicate for E's default initialization.
         --  We do not generate default initialization for unconstrained types.

         if Can_Be_Default_Initialized (E) then
            Create_Default_Init_Assumption (File.Cur_Theory, E);
         end if;
      end if;

      if Has_Predicates (E) then
         Create_Dynamic_Predicate (File.Cur_Theory, E);
      end if;

      --  If E is a scalar type with dynamic bounds, we give axioms for the
      --  values of its bounds.

      if not Is_Itype (E) and then Is_Scalar_Type (E) then
         Create_Axioms_For_Scalar_Bounds (File.Cur_Theory, E);
      end if;

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity => E);
   end Generate_Type_Completion;

   -----------------------
   -- Ident_Of_Ada_Type --
   -----------------------

   function Ident_Of_Ada_Type (E : Entity_Id) return W_Name_Id is
   begin
      if Is_Standard_Boolean_Type (E) then
         return Get_Name (EW_Bool_Type);
      else
         return To_Why_Type (E);
      end if;
   end Ident_Of_Ada_Type;

   --------------------
   -- Translate_Type --
   --------------------

   procedure Translate_Type
     (File       : in out Why_Section;
      E          : Entity_Id;
      New_Theory : out Boolean)
   is
      procedure Translate_Underlying_Type
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id);
      --  Translate a non-private type entity E

      -------------------------------
      -- Translate_Underlying_Type --
      -------------------------------

      procedure Translate_Underlying_Type
        (Theory : W_Theory_Declaration_Id;
         E      : Entity_Id) is
      begin
         case Ekind (E) is
            when Scalar_Kind =>
               Declare_Scalar_Type (Theory, E);

            when Array_Kind =>
               Declare_Ada_Array (Theory, E);

            when E_Record_Type
               | E_Record_Subtype
               | Concurrent_Kind =>
               Declare_Ada_Record (File, Theory, E);

            when E_Class_Wide_Type | E_Class_Wide_Subtype =>
               Add_Use_For_Entity (File, Specific_Tagged (E),
                                   EW_Export, With_Completion => False);

            when Private_Kind =>
               pragma Assert (Full_View_Not_In_SPARK (E));
               pragma Assert (not Entity_In_SPARK (Underlying_Type (E)));
               Declare_Ada_Record (File, Theory, E);

            when others =>
               Ada.Text_IO.Put_Line ("[Translate_Underlying_Type] ekind ="
                                     & Entity_Kind'Image (Ekind (E)));
               raise Not_Implemented;
         end case;
      end Translate_Underlying_Type;

   --  Start of processing for Translate_Type

   begin
      if Is_Standard_Boolean_Type (E) or else E = Universal_Fixed then
         New_Theory := False;
         return;

      else
         if Is_Array_Type (E) then
            Create_Rep_Array_Theory_If_Needed (File, E);
         end if;

         New_Theory := True;

         Open_Theory
           (File, E_Module (E),
            Comment =>
              "Module for axiomatizing type "
            & """" & Get_Name_String (Chars (E)) & """"
            & (if Sloc (E) > 0 then
                 " defined at " & Build_Location_String (Sloc (E))
              else "")
            & ", created in " & GNAT.Source_Info.Enclosing_Entity);

         Translate_Underlying_Type (File.Cur_Theory, Retysp (E));

         --  We declare a default value for all types, in principle.
         --  Cloned subtypes are a special case, they do not need such a
         --  definition.

         if Is_Record_Type (E) and then
           Ekind (E) not in E_Class_Wide_Type | E_Class_Wide_Subtype and then
           (if Ekind (E) = E_Record_Subtype then
                not (Present (Cloned_Subtype (E))))
         then
            Emit
              (File.Cur_Theory,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Dummy)),
                  Binders     => (1 .. 0 => <>),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type =>
                    +New_Named_Type (Name => To_Why_Type (E, Local => True))));
         end if;

         --  We generate a record type containing only one mutable field of
         --  type t. This is used to store mutable variables of type t.
         --  We also generate a havoc function for this type.
         --  We do not generate these declarations for record types which are
         --  clones of existing types and
         --  statically constrained array type are no new type is declared for
         --  them.

         if (not Has_Record_Type (E)
               or else not Record_Type_Is_Clone (Retysp (E)))
           and then (not Has_Array_Type (E)
                     or else not Is_Static_Array_Type (Retysp (E)))
         then
            Emit_Ref_Type_Definition
              (Theory => File.Cur_Theory,
               Name   => To_Why_Type (Retysp (E), Local => True));
            Emit
              (File.Cur_Theory,
               New_Havoc_Declaration
                 (Name => To_Why_Type (Retysp (E), Local => True)));
         end if;

         --  If E is the full view of a private type, use its partial view as
         --  the filtering entity, as it is the entity used everywhere in AST.

         if Is_Full_View (E) then
            Close_Theory (File,
                          Kind => Definition_Theory,
                          Defined_Entity => Partial_View (E));
         else
            Close_Theory (File,
                          Kind => Definition_Theory,
                          Defined_Entity => E);
         end if;
      end if;
   end Translate_Type;

end Gnat2Why.Types;
