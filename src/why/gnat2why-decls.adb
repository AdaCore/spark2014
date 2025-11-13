------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
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

with Ada.Strings;          use Ada.Strings;
with Ada.Strings.Fixed;    use Ada.Strings.Fixed;
with GNAT.Source_Info;
with GNATCOLL.Symbols;
with Gnat2Why.Expr;        use Gnat2Why.Expr;
with Gnat2Why.Util;        use Gnat2Why.Util;
with Namet;                use Namet;
with Sinput;               use Sinput;
with SPARK_Util.Hardcoded; use SPARK_Util.Hardcoded;
with Types;                use Types;
with Uintp;                use Uintp;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Modules;    use Why.Atree.Modules;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Gen.Hardcoded;    use Why.Gen.Hardcoded;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Pointers;     use Why.Gen.Pointers;
with Why.Gen.Terms;        use Why.Gen.Terms;
with Why.Ids;              use Why.Ids;
with Why.Inter;            use Why.Inter;
with Why.Sinfo;            use Why.Sinfo;
with Why.Types;            use Why.Types;

package body Gnat2Why.Decls is

   ------------------------
   -- Translate_Constant --
   ------------------------

   procedure Translate_Constant (E : Object_Kind_Id) is
      B  : constant Item_Type := Ada_Ent_To_Why.Element (Symbol_Table, E);
      pragma Assert (B.Kind = Regular and then not B.Main.Mutable);
      Th : Theory_UC;
   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Th :=
        Open_Theory
          (WF_Context,
           E_Module (E),
           Comment =>
             "Module for defining the constant "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a "logic", whose axiom will be given in a completion

      Emit
        (Th,
         Why.Atree.Builders.New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (B.Main.B_Name),
            Binders     => (1 .. 0 => <>),
            Labels      => Get_Counterexample_Labels (E),
            Location    => Safe_First_Sloc (E),
            Return_Type => Get_Typ (B.Main.B_Name)));

      --  Generate a constant for the validity flag

      if B.Valid.Present then
         Emit
           (Th,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (B.Valid.Id),
               Binders     => (1 .. 0 => <>),
               Labels      => Get_Counterexample_Labels (E, "'" & Valid_Label),
               Location    => Safe_First_Sloc (E),
               Return_Type => Get_Typ (B.Valid.Id)));
      end if;

      Close_Theory (Th, Kind => Definition_Theory, Defined_Entity => E);
   end Translate_Constant;

   ------------------------------
   -- Translate_Constant_Value --
   ------------------------------

   procedure Translate_Constant_Value (E : E_Constant_Id) is
      Decl : constant N_Object_Declaration_Id := Enclosing_Declaration (E);
      Expr : constant Opt_N_Subexpr_Id := Expression (Decl);

      --  Always use the Ada type for the equality between the constant result
      --  and the translation of its initialization expression. Using "int"
      --  instead is tempting to facilitate the job of automatic provers, but
      --  it is potentially incorrect. For example for:

      --    C : constant Natural := Largest_Int + 1;

      --  we should *not* generate the incorrect axiom:

      --    axiom c__def:
      --      to_int(c) = to_int(largest_int) + 1

      --  but the correct one:

      --    axiom c__def:
      --      c = of_int (to_int(largest_int) + 1)

      Th : Theory_UC;
   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Th :=
        Open_Theory
          (WF_Context,
           E_Module (E, Axiom),
           Comment =>
             "Module for defining the value of constant "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If the constant is hardcoded, get its definition

      if Is_Hardcoded_Entity (E) then
         declare
            B   : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, E);
            pragma Assert (B.Kind = Regular and then not B.Main.Mutable);
            Def : constant W_Term_Id := Hardcoded_Constant_Value (E);

         begin
            if Def /= Why_Empty then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Ada_Node => E,
                     Name     => B.Main.B_Name,
                     Binders  => (1 .. 0 => <>),
                     Def      => Def));

            end if;
         end;

      --  Default values of parameters are not considered as the value of the
      --  constant representing the parameter. We do not generate an axiom
      --  for constants inserted by the compiler, as their initialization
      --  expression may not be expressible as a logical term (e.g., it may
      --  include X'Loop_Entry for a constant inserted in a block of actions).
      --  We also check for the presence of calls to volatile functions,
      --  functions with side effects and allocators which we can't handle in
      --  axioms.
      --  Finally we check if we are in a protected object, as in that case the
      --  expression may require the "self" object, but it's not set up here.
      --  Static expressions can't reference "self", so they are fine.

      elsif Present (Expr)
        and then not Expression_Contains_Old_Or_Loop_Entry (Expr)
        and then not Contains_Volatile_Function_Call (Expr)
        and then not Is_Function_Call_With_Side_Effects (Expr)
        and then not Contains_Allocator (Expr)
        and then (not Within_Protected_Type (E)
                  or else Is_Static_Expression (Expr))
      then
         declare
            B      : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, E);
            pragma Assert (B.Kind = Regular and then not B.Main.Mutable);
            Params : constant Transformation_Params :=
              (Logic_Params with delta Ref_Allowed => True);
            Def    : W_Term_Id;

            --  Context and validity flag to handle potantially invalid values

            Valid_Flag : W_Expr_Id :=
              (if B.Valid.Present
               then +New_Valid_Value_For_Type (Etype (E))
               else Why_Empty);
            Context    : Ref_Context;

         begin
            --  Handle the potential propagation of invalid values

            if Propagates_Validity_Flag (Decl) then
               pragma Assert (B.Valid.Present);
               Def :=
                 +Transform_Potentially_Invalid_Expr
                    (Expr          => Expr,
                     Expected_Type => Get_Typ (B.Main.B_Name),
                     Domain        => EW_Term,
                     Params        => Params,
                     Context       => Context,
                     Valid_Flag    => Valid_Flag);
            else
               Def := Transform_Term (Expr, Get_Typ (B.Main.B_Name), Params);
            end if;

            --  We will generate separate defining axioms, so insert the
            --  context inside Def and Valid_Flag.

            if B.Valid.Present then
               Def :=
                 +Bindings_For_Ref_Context
                    (Expr => +Def, Context => Context, Domain => EW_Term);

               if Propagates_Validity_Flag (Decl)
                 and then Is_Potentially_Invalid_Expr (Expr)
               then
                  Valid_Flag :=
                    Bindings_For_Ref_Context
                      (Expr    => Valid_Flag,
                       Context => Context,
                       Domain  => EW_Term);
               end if;
            end if;

            --  Emit an axiom for the definition of B.Main if Def does not
            --  contain any dereferences.

            if not Has_Dereference_Or_Any_Or_Self (Def) then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Ada_Node => E,
                     Name     => B.Main.B_Name,
                     Binders  => (1 .. 0 => <>),
                     Def      => Def));
            end if;

            --  Also add an axioms of B.Valid.Id if any

            if B.Valid.Present
              and then not Has_Dereference_Or_Any_Or_Self (+Valid_Flag)
            then
               Emit
                 (Th,
                  New_Defining_Axiom
                    (Ada_Node => E,
                     Name     => B.Valid.Id,
                     Binders  => (1 .. 0 => <>),
                     Def      => +Valid_Flag));
            end if;
         end;

      end if;

      --  No filtering is necessary here, as the theory should on the
      --  contrary use the previously defined theory for the partial
      --  view. Attach the newly created theory as a completion of the
      --  existing one.

      Close_Theory
        (Th,
         Kind           => Axiom_Theory,
         Defined_Entity => (if Is_Full_View (E) then Partial_View (E) else E));
   end Translate_Constant_Value;

   --------------------------
   -- Translate_Exceptions --
   --------------------------

   procedure Translate_Exceptions is
      Th : Theory_UC;
      V  : Int := 1;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           Module  => Exception_Module,
           Comment =>
             "Module declaring the Ada exceptions, created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  Declare a distinct constant for all Ada exceptions

      for E of All_Exceptions loop
         Emit
           (Th,
            New_Function_Decl
              (Name        => To_Why_Id (E, Local => True),
               Domain      => EW_Pterm,
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Int_Type,
               Def         =>
                 New_Integer_Constant (Value => UI_From_Int (V))));
         V := V + 1;
      end loop;

      Close_Theory (Th, Kind => Standalone_Theory);
   end Translate_Exceptions;

   -------------------------------
   -- Translate_External_Object --
   -------------------------------

   procedure Translate_External_Object (E : Entity_Name) is
      Object_Name : constant String := To_String (E);
      Th          : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           Module  =>
             New_Module
               (Name => Object_Name, File => GNATCOLL.Symbols.No_Symbol),
           Comment =>
             "Module declaring the external object """
             & Object_Name
             & ","" created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  Do not set a location as counterexample values for external objects
      --  are not meaningful.

      Emit
        (Th,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Labels   => Symbol_Sets.Empty_Set,
            Location => No_Location,
            Ref_Type => EW_Private_Type));

      Close_Theory (Th, Kind => Standalone_Theory);
   end Translate_External_Object;

   ---------------------------
   -- Translate_Loop_Entity --
   ---------------------------

   procedure Translate_Loop_Entity (E : E_Loop_Id) is
      Th : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           E_Module (E),
           Comment =>
             "Module for defining "
             & "the loop exit exception for the loop "
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
         New_Exception_Declaration
           (Name =>
              Loop_Exception_Name (E, Is_Continue => False, Local => True),
            Arg  => Why_Empty));
      Emit
        (Th,
         New_Exception_Declaration
           (Name =>
              Loop_Exception_Name (E, Is_Continue => True, Local => True),
            Arg  => Why_Empty));

      Close_Theory (Th, Kind => Standalone_Theory);
   end Translate_Loop_Entity;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable (E : Object_Kind_Id) is
      Var      : constant Item_Type := Mk_Item_Of_Entity (E);
      Alias    : constant Opt_Object_Kind_Id := Ultimate_Overlaid_Entity (E);
      Alias_Id : constant W_Identifier_Id :=
        (if Present (Alias)
         then
           New_Temp_Identifier
             (Base_Name => "overlaid", Typ => Type_Of_Node (Alias))
         else Why_Empty);
      Th       : Theory_UC;

      procedure Emit_Global_Ref_Or_Function
        (Name : W_Identifier_Id; Mutable : Boolean; Labels : Symbol_Sets.Set);
      --  Declare a part of the object E. Emit a constant declaration if the
      --  object is not mutable, a global reference if it is mutable but not
      --  an overlay, and a function taking the overlaid object as a parameter
      --  for mutable parts of overlays.

      ---------------------------------
      -- Emit_Global_Ref_Or_Function --
      ---------------------------------

      procedure Emit_Global_Ref_Or_Function
        (Name : W_Identifier_Id; Mutable : Boolean; Labels : Symbol_Sets.Set)
      is
      begin
         --  For non-mutable objects, always generate a constant

         if not Mutable then
            Emit
              (Th,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (Name),
                  Binders     => (1 .. 0 => <>),
                  Labels      => Labels,
                  Location    => Safe_First_Sloc (E),
                  Return_Type => Get_Typ (Name)));

         --  If the object is not aliased, generate a global ref

         elsif No (Alias) then
            Emit
              (Th,
               New_Global_Ref_Declaration
                 (Name     => To_Local (Name),
                  Labels   => Labels,
                  Location => Safe_First_Sloc (E),
                  Ref_Type => Get_Typ (Name)));

         --  Otherwise, generate a function that takes Alias_Id as a parameter

         else
            Emit
              (Th,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (Name),
                  Binders     =>
                    (1 =>
                       New_Binder
                         (Domain   => EW_Pterm,
                          Name     => Alias_Id,
                          Arg_Type => Get_Typ (Alias_Id))),
                  Labels      => Labels,
                  Location    => Safe_First_Sloc (E),
                  Return_Type => Get_Typ (Name)));
         end if;
      end Emit_Global_Ref_Or_Function;

   begin
      Th :=
        Open_Theory
          (WF_Context,
           E_Module (E),
           Comment =>
             "Module for defining a ref holding the value of variable "
             & """"
             & Get_Name_String (Chars (E))
             & """"
             & (if Sloc (E) > 0
                then " defined at " & Build_Location_String (Sloc (E))
                else "")
             & ", created in "
             & GNAT.Source_Info.Enclosing_Entity);

      --  If E is not in SPARK, only declare an object of type __private for
      --  use in effects of program functions in Why3.

      case Var.Kind is
         when DRecord                =>
            if Var.Fields.Present then

               --  Generate a global ref for the fields

               Emit_Global_Ref_Or_Function
                 (Name    => Var.Fields.Binder.B_Name,
                  Labels  =>
                    Get_Counterexample_Labels
                      (E, Append_To_Name => "'" & Field_Label),
                  Mutable => True);
            end if;

            if Var.Discrs.Present then

               --  Generate a global ref or constant for the fields

               Emit_Global_Ref_Or_Function
                 (Name    => Var.Discrs.Binder.B_Name,
                  Labels  =>
                    Get_Counterexample_Labels
                      (E, Append_To_Name => "'" & Discr_Label),
                  Mutable => Var.Discrs.Binder.Mutable);
            end if;

            if Var.Constr.Present then

               --  Generate a constant for 'Constrained attribute

               Emit_Global_Ref_Or_Function
                 (Name    => Var.Constr.Id,
                  Labels  =>
                    Get_Counterexample_Labels (E, "'" & Constrained_Label),
                  Mutable => False);
            end if;

            if Var.Tag.Present then

               --  Generate a constant for 'Tag attribute

               Emit_Global_Ref_Or_Function
                 (Name    => Var.Tag.Id,
                  Labels  => Symbol_Sets.Empty_Set,
                  Mutable => False);
            end if;

         when UCArray                =>

            --  Generate a global ref for the content

            Emit_Global_Ref_Or_Function
              (Name    => Var.Content.B_Name,
               Labels  => Get_Counterexample_Labels (E),
               Mutable => True);

            for D in 1 .. Var.Dim loop
               declare
                  function Bound_Dimension_To_Str
                    (Total_Dim, Num_Dim : Integer; Bound_Name : String)
                     return String
                  is (if Total_Dim = 1
                      then Bound_Name
                      else
                        Bound_Name
                        & " ("
                        & Trim (Integer'Image (Num_Dim), Both)
                        & ")");

               begin
                  --  Generate constants for bounds

                  Emit_Global_Ref_Or_Function
                    (Name    => Var.Bounds (D).First,
                     Labels  =>
                       Get_Counterexample_Labels
                         (E,
                          Bound_Dimension_To_Str
                            (Var.Dim, D, "'" & First_Label)),
                     Mutable => False);

                  Emit_Global_Ref_Or_Function
                    (Name    => Var.Bounds (D).Last,
                     Labels  =>
                       Get_Counterexample_Labels
                         (E,
                          Bound_Dimension_To_Str
                            (Var.Dim, D, "'" & Last_Label)),
                     Mutable => False);
               end;
            end loop;

         when Pointer                =>

            --  Generate a global ref for the value

            Emit_Global_Ref_Or_Function
              (Name    => Var.Value.B_Name,
               Labels  => Get_Counterexample_Labels (E, "'" & All_Label),
               Mutable => True);

            --  Generate a global ref for the is_null if the pointer is mutable

            Emit_Global_Ref_Or_Function
              (Name    => Var.Is_Null,
               Labels  => Get_Counterexample_Labels (E, "'" & Is_Null_Label),
               Mutable => Var.Mutable);

         when Regular                =>
            begin
               --  Currently only generate values for scalar variables in
               --  counterexamples, which are always of the Regular kind.

               --  generate a global ref

               Emit_Global_Ref_Or_Function
                 (Name    => Var.Main.B_Name,
                  Labels  => Get_Counterexample_Labels (E),
                  Mutable => True);
            end;

         when Subp | Concurrent_Self =>
            raise Program_Error;
      end case;

      --  generate a global ref for the initialization flag if any

      if Var.Init.Present then
         Emit_Global_Ref_Or_Function
           (Name    => Var.Init.Id,
            Labels  => Get_Counterexample_Labels (E, "'" & Initialized_Label),
            Mutable => True);
      end if;

      --  Generate a variable for the move tree

      if Var.Is_Moved.Present then
         Emit_Global_Ref_Or_Function
           (Name    => Var.Is_Moved.Id,
            Labels  => Symbol_Sets.Empty_Set,
            Mutable => True);
      end if;

      --  Generate a variable for the validity flag

      if Var.Valid.Present then
         Emit_Global_Ref_Or_Function
           (Name    => Var.Valid.Id,
            Labels  => Get_Counterexample_Labels (E, "'" & Valid_Label),
            Mutable => True);
      end if;

      --  Declare the variable for the value at end of E

      if Is_Local_Borrower (E) then
         Declare_At_End_Ref (Th, E);
      end if;

      Close_Theory (Th, Kind => Definition_Theory, Defined_Entity => E);
   end Translate_Variable;

end Gnat2Why.Decls;
