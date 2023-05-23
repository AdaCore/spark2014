------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Ada.Strings;         use Ada.Strings;
with Ada.Strings.Fixed;   use Ada.Strings.Fixed;
with GNAT.Source_Info;
with GNATCOLL.Symbols;
with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Gnat2Why.Util;       use Gnat2Why.Util;
with Namet;               use Namet;
with Sinput;              use Sinput;
with Types;               use Types;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Pointers;    use Why.Gen.Pointers;
with Why.Ids;             use Why.Ids;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

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

      Th := Open_Theory
        (WF_Context, E_Module (E),
         Comment =>
           "Module for defining the constant "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a "logic", whose axiom will be given in a completion

      Emit (Th,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (B.Main.B_Name),
               Binders     => (1 .. 0 => <>),
               Labels      => Get_Counterexample_Labels (E),
               Location    => Safe_First_Sloc (E),
               Return_Type => Get_Typ (B.Main.B_Name)));

      Close_Theory (Th,
                    Kind           => Definition_Theory,
                    Defined_Entity => E);
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

      Th := Open_Theory
        (WF_Context,
         E_Axiom_Module (E),
         Comment =>
           "Module for defining the value of constant "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Default values of parameters are not considered as the value of the
      --  constant representing the parameter. We do not generate an axiom
      --  for constants inserted by the compiler, as their initialization
      --  expression may not be expressible as a logical term (e.g., it may
      --  include X'Loop_Entry for a constant inserted in a block of actions).
      --  We also check for the presence of calls to volatile functions and
      --  allocators which we can't handle in axioms.
      --  Finally we check if we are in a protected object, as in that case the
      --  expression may require the "self" object, but it's not set up here.
      --  Static expressions can't reference "self", so they are fine.

      if Present (Expr)
        and then not Expression_Contains_Old_Or_Loop_Entry (Expr)
        and then not Contains_Volatile_Function_Call (Expr)
        and then not Contains_Allocator (Expr)
        and then (not Within_Protected_Type (E)
                  or else Is_Static_Expression (Expr))
      then
         declare
            B  : constant Item_Type :=
              Ada_Ent_To_Why.Element (Symbol_Table, E);
            pragma Assert (B.Kind = Regular and then not B.Main.Mutable);
            Def : W_Term_Id;

         begin
            Def := Get_Pure_Logic_Term_If_Possible
              (Expr, Get_Typ (B.Main.B_Name));

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

      end if;

      --  No filtering is necessary here, as the theory should on the
      --  contrary use the previously defined theory for the partial
      --  view. Attach the newly created theory as a completion of the
      --  existing one.

      Close_Theory (Th,
                    Kind           => Axiom_Theory,
                    Defined_Entity =>
                      (if Is_Full_View (E) then Partial_View (E) else E));
      Register_Dependency_For_Soundness
        (E_Axiom_Module (E), Enclosing_Unit (E));
   end Translate_Constant_Value;

   -------------------------------
   -- Translate_External_Object --
   -------------------------------

   procedure Translate_External_Object (E : Entity_Name) is
      Object_Name : constant String := To_String (E);
      Th : Theory_UC;
   begin
      Th :=
        Open_Theory
          (WF_Context,
           Module =>
             New_Module (Name => Object_Name,
                         File => GNATCOLL.Symbols.No_Symbol),
           Comment =>
             "Module declaring the external object """ & Object_Name &
             ","" created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Do not set a location as counterexample values for external objects
      --  are not meaningful.

      Emit
        (Th,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Labels   => Symbol_Sets.Empty_Set,
            Location => No_Location,
            Ref_Type => EW_Private_Type));

      Close_Theory (Th,
                    Kind => Standalone_Theory);
   end Translate_External_Object;

   ---------------------------
   -- Translate_Loop_Entity --
   ---------------------------

   procedure Translate_Loop_Entity (E : E_Loop_Id) is
      Th : Theory_UC;
   begin
      Th := Open_Theory
        (WF_Context, E_Module (E),
         Comment =>
           "Module for defining "
         & "the loop exit exception for the loop "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (Th,
            New_Exception_Declaration
              (Name => Loop_Exception_Name (E, Local => True),
               Arg  => Why_Empty));

      Close_Theory (Th,
                    Kind => Standalone_Theory);
   end Translate_Loop_Entity;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable (E : Object_Kind_Id) is
      Var : constant Item_Type := Mk_Item_Of_Entity (E);
      Th : Theory_UC;
   begin
      Th := Open_Theory
        (WF_Context,
         E_Module (E),
         Comment =>
           "Module for defining a ref holding the value of variable "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  If E is not in SPARK, only declare an object of type __private for
      --  use in effects of program functions in Why3.

      case Var.Kind is
         when DRecord =>
            if Var.Fields.Present then

               --  Generate a global ref for the fields

               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Name     => To_Local (Var.Fields.Binder.B_Name),
                     Labels   => Get_Counterexample_Labels
                          (E, Append_To_Name => "'" & Field_Label),
                     Location => Safe_First_Sloc (E),
                     Ref_Type => Get_Typ (Var.Fields.Binder.B_Name)));
            end if;

            if Var.Discrs.Present then

               --  Generate a global ref or constant for the fields

               if Var.Discrs.Binder.Mutable then
                  Emit
                    (Th,
                     New_Global_Ref_Declaration
                       (Name     => To_Local (Var.Discrs.Binder.B_Name),
                        Labels   => Get_Counterexample_Labels
                          (E, Append_To_Name => "'" & Discr_Label),
                        Location => Safe_First_Sloc (E),
                        Ref_Type => Get_Typ (Var.Discrs.Binder.B_Name)));
               else
                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Pterm,
                        Name        =>
                          To_Local (Var.Discrs.Binder.B_Name),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Get_Counterexample_Labels
                          (E, Append_To_Name => "'" & Discr_Label),
                        Location    => Safe_First_Sloc (E),
                        Return_Type => Get_Typ (Var.Discrs.Binder.B_Name)));
               end if;
            end if;

            if Var.Constr.Present then

               --  Generate a constant for 'Constrained attribute

               Emit
                 (Th,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (Var.Constr.Id),
                     Binders     => (1 .. 0 => <>),
                     Labels      => Get_Counterexample_Labels
                       (E, "'" & Constrained_Label),
                     Location    => Safe_First_Sloc (E),
                     Return_Type => Get_Typ (Var.Constr.Id)));
            end if;

            if Var.Tag.Present then

               --  Generate a constant for 'Tag attribute

               Emit
                 (Th,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (Var.Tag.Id),
                     Binders     => (1 .. 0 => <>),
                     Labels      => Symbol_Sets.Empty_Set,
                     Location    => Safe_First_Sloc (E),
                     Return_Type => Get_Typ (Var.Tag.Id)));
            end if;

            if Var.Is_Moved_R.Present then

               --  Generate a variable for Is_Moved flag

               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Name     => To_Local (Var.Is_Moved_R.Id),
                     Location => Safe_First_Sloc (E),
                     Labels   => Symbol_Sets.Empty_Set,
                     Ref_Type => Get_Typ (Var.Is_Moved_R.Id)));
            end if;

         when UCArray =>

            --  Generate a global ref for the content

            Emit
              (Th,
               New_Global_Ref_Declaration
                 (Name     => To_Local (Var.Content.B_Name),
                  Labels   => Get_Counterexample_Labels (E),
                  Location => Safe_First_Sloc (E),
                  Ref_Type => Get_Typ (Var.Content.B_Name)));

            for D in 1 .. Var.Dim loop
               declare
                  function Bound_Dimension_To_Str
                    (Total_Dim, Num_Dim : Integer;
                     Bound_Name : String) return String
                  is
                    (if Total_Dim = 1 then Bound_Name
                     else Bound_Name &
                       " (" & Trim (Integer'Image (Num_Dim), Both) &
                       ")");

                  Ty_First : constant W_Type_Id :=
                    Get_Typ (Var.Bounds (D).First);
                  Ty_Last  : constant W_Type_Id :=
                    Get_Typ (Var.Bounds (D).Last);

               begin
                  --  Generate constants for bounds

                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Pterm,
                        Name        => To_Local (Var.Bounds (D).First),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Get_Counterexample_Labels
                          (E, Bound_Dimension_To_Str
                               (Var.Dim, D, "'" & First_Label)),
                        Location    => Safe_First_Sloc (E),
                        Return_Type => Ty_First));

                  Emit
                    (Th,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Pterm,
                        Name        => To_Local (Var.Bounds (D).Last),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Get_Counterexample_Labels
                          (E, Bound_Dimension_To_Str
                               (Var.Dim, D, "'" & Last_Label)),
                        Location    => Safe_First_Sloc (E),
                        Return_Type => Ty_Last));
               end;
            end loop;

         when Pointer =>

            --  Generate a global ref for the value

            Emit
              (Th,
               New_Global_Ref_Declaration
                 (Name     => To_Local (Var.Value.B_Name),
                  Location => Safe_First_Sloc (E),
                  Labels   => Get_Counterexample_Labels (E, "'" & All_Label),
                  Ref_Type => Get_Typ (Var.Value.B_Name)));

            --  Generate a global ref for the is_null if the pointer is mutable

            if Var.Mutable then
               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Name     => To_Local (Var.Is_Null),
                     Location => Safe_First_Sloc (E),
                     Labels   => Get_Counterexample_Labels
                       (E, "'" & Is_Null_Label),
                     Ref_Type => Get_Typ (Var.Is_Null)));

            --  Otherwise generate a constant

            else
               Emit
                 (Th,
                  Why.Atree.Builders.New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (Var.Is_Null),
                     Binders     => (1 .. 0 => <>),
                     Location    => Safe_First_Sloc (E),
                     Labels      => Get_Counterexample_Labels
                       (E, "'" & Is_Null_Label),
                     Return_Type => Get_Typ (Var.Is_Null)));
            end if;

            Emit
              (Th,
               New_Global_Ref_Declaration
                 (Name     => To_Local (Var.Is_Moved),
                  Location => Safe_First_Sloc (E),
                  Labels   => Symbol_Sets.Empty_Set,
                  Ref_Type => Get_Typ (Var.Is_Moved)));

         when Regular =>
            begin
               --  Currently only generate values for scalar variables in
               --  counterexamples, which are always of the Regular kind.

               --  generate a global ref

               Emit
                 (Th,
                  New_Global_Ref_Declaration
                    (Name     => To_Local (Var.Main.B_Name),
                     Labels   => Get_Counterexample_Labels (E),
                     Location => Safe_First_Sloc (E),
                     Ref_Type => Get_Typ (Var.Main.B_Name)));
            end;

         when Func | Concurrent_Self =>
            raise Program_Error;
      end case;

      --  generate a global ref for the initialization flag if any

      if Var.Init.Present then
         Emit
           (Th,
            New_Global_Ref_Declaration
              (Name     => To_Local (Var.Init.Id),
               Labels   => Get_Counterexample_Labels
                 (E, "'" & Initialized_Label),
               Location => Safe_First_Sloc (E),
               Ref_Type => EW_Bool_Type));
      end if;

      --  Declare the variable for the value at end of E

      if Is_Local_Borrower (E) then
         Declare_At_End_Ref (Th, E);
      end if;

      Close_Theory (Th,
                    Kind           => Definition_Theory,
                    Defined_Entity => E);
   end Translate_Variable;

end Gnat2Why.Decls;
