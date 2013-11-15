------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
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

with Atree;               use Atree;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Sinfo;               use Sinfo;
with Sinput;              use Sinput;
with Snames;              use Snames;
with String_Utils;        use String_Utils;

with SPARK_Util;          use SPARK_Util;

with Why.Ids;             use Why.Ids;
with Why.Sinfo;           use Why.Sinfo;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

package body Gnat2Why.Decls is

   function Mk_Item_Of_Entity
     (E    : Entity_Id;
      Name : W_Identifier_Id) return Item_Type;

   -------------------------
   -- Mk_Item_From_Entity --
   -------------------------

   function Mk_Item_Of_Entity
     (E    : Entity_Id;
      Name : W_Identifier_Id)
     return Item_Type
   is
      Binder   : constant Binder_Type :=
        Binder_Type'(Ada_Node => E,
                     B_Name   => Name,
                     B_Ent    => null,
                     Mutable  => Is_Mutable_In_Why (E));
   begin
      if Ekind (E) in Formal_Kind
        and then Is_Array_Type (Etype (E))
        and then not Is_Static_Array_Type (Etype (E))
      then
         declare
            Result : Item_Type :=
              (Kind   => UCArray,
               Main   => Binder,
               Dim    => Natural (Number_Dimensions (Etype (E))),
               Bounds => (others => <>));
            Index  : Node_Id := First_Index (Etype (E));
         begin
            for D in 1 .. Result.Dim loop
               Result.Bounds (D).First :=
                 Attr_Append (Name, Attribute_First, D,
                              EW_Abstract (Base_Type (Etype (Index))));
               Result.Bounds (D).Last :=
                 Attr_Append (Name, Attribute_Last, D,
                              EW_Abstract (Base_Type (Etype (Index))));
               Next_Index (Index);
            end loop;
            return Result;
         end;
      else
         return (Regular, Binder);
      end if;
   end Mk_Item_Of_Entity;

   ------------------------------
   -- Translate_Abstract_State --
   ------------------------------

   procedure Translate_Abstract_State
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name     : constant String := Full_Name (E);
      Typ      : constant W_Type_Id := EW_Private_Type;
      Why_Name : constant W_Identifier_Id := To_Why_Id (E => E, Typ => Typ);
      Decl     : constant W_Declaration_Id :=
        New_Type_Decl (Name  => To_Ident (WNE_Type),
                       Alias => Typ);
      Var      : constant Item_Type := Mk_Item_Of_Entity (E, Why_Name);

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining a ref holding the value "
                       & "of abstract state "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an alias for the name of the object's type, based on the
      --  name of the object. This is useful when generating logic functions
      --  from Ada functions, to generate additional parameters for the global
      --  objects read.

      Emit (File.Cur_Theory, Decl);

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Labels   => Name_Id_Sets.Empty_Set,
            Ref_Type => New_Named_Type (To_Ident (WNE_Type))));

      Insert_Item (E, Var);

      Close_Theory (File,
                    Kind => Standalone_Theory);
   end Translate_Abstract_State;

   ------------------------
   -- Translate_Constant --
   ------------------------

   procedure Translate_Constant
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String := Base_Name;
      Typ       : constant W_Type_Id := EW_Abstract (Etype (E));

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a "logic", whose axiom will be given in a completion

      Emit (File.Cur_Theory,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Domain => EW_Term, Local => True),
               Binders     => (1 .. 0 => <>),
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Typ));
      Insert_Entity (E, To_Why_Id (E, Typ => Typ));
      Close_Theory (File,
                    Kind => Definition_Theory,
                    Defined_Entity => E);
   end Translate_Constant;

   ------------------------------
   -- Translate_Constant_Value --
   ------------------------------

   procedure Translate_Constant_Value
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String := Base_Name & Axiom_Theory_Suffix;
      Typ    : constant W_Type_Id := EW_Abstract (Etype (E));
      Decl   : constant Node_Id := Parent (E);
      Def    : W_Term_Id;

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

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name,
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

      if Ekind (E) /= E_In_Parameter
        and then Present (Expression (Decl))
        and then Comes_From_Source (E)
      then
         Def := Get_Pure_Logic_Term_If_Possible
           (File, Expression (Decl), Typ);
      else
         Def := Why_Empty;
      end if;

      if Def /= Why_Empty then

         --  The definition of constants is done in a separate theory. This
         --  theory is added as a completion of the base theory defining the
         --  constant.

         if Is_Full_View (E) then

            --  It may be the case that the full view has a more precise type
            --  than the partial view, for example when the type of the partial
            --  view is an indefinite array. In that case, convert back to the
            --  expected type for the constant.

            if Etype (Partial_View (E)) /= Etype (E) then
               Def := W_Term_Id (Insert_Simple_Conversion
                        (Domain   => EW_Term,
                         Ada_Node => Expression (Decl),
                         Expr     => W_Expr_Id (Def),
                         To       => EW_Abstract (Etype (Partial_View (E)))));
            end if;

            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

         --  In the general case, we generate a defining axiom if necessary and
         --  possible.

         else
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));
         end if;
      end if;

      --  No filtering is necessary here, as the theory should on the
      --  contrary use the previously defined theory for the partial
      --  view. Attach the newly created theory as a completion of the
      --  existing one.

      Close_Theory (File,
                    Kind => Axiom_Theory,
                    Defined_Entity =>
                      (if Is_Full_View (E) then Partial_View (E) else E));
   end Translate_Constant_Value;

   -------------------------------
   -- Translate_External_Object --
   -------------------------------

   procedure Translate_External_Object (E : Entity_Name) is
      File : Why_Section := Why_Sections (WF_Variables);
   begin
      Open_Theory
        (File, Capitalize_First (E.all),
         Comment =>
           "Module declaring the external object """ & E.all &
           ","" created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_With_Clause (File.Cur_Theory, Ref_Module, EW_Import, EW_Module);

      Emit (File.Cur_Theory,
            New_Type_Decl (Name   => To_Ident (WNE_Type),
                           Labels => Name_Id_Sets.Empty_Set));
      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E.all, Local => True),
            Labels   => Name_Id_Sets.Empty_Set,
            Ref_Type => New_Named_Type (Name => To_Ident (WNE_Type))));

      Close_Theory (File,
                    Kind => Standalone_Theory);
   end Translate_External_Object;

   ---------------------------
   -- Translate_Loop_Entity --
   ---------------------------

   procedure Translate_Loop_Entity
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name : constant String := Full_Name (E);
   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the loop exit exception for the loop"
                   & """" & Get_Name_String (Chars (E)) & """"
                   & (if Sloc (E) > 0 then
                     " defined at " & Build_Location_String (Sloc (E))
                     else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (File.Cur_Theory,
            New_Exception_Declaration (Name => To_Why_Id (E, Local => True),
                                       Arg  => Why_Empty));

      Close_Theory (File,
                    Kind => Standalone_Theory);
   end Translate_Loop_Entity;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable
     (File : in out Why_Section;
      E     : Entity_Id)
   is
      Name : constant String := Full_Name (E);

      --  We first build the type that we use in Why; this may be e.g. String

      Use_Ty : constant W_Type_Id := EW_Abstract (Etype (E));

      Typ  : constant W_Type_Id :=
        (if Ekind (E) = E_Loop_Parameter then
           EW_Int_Type
         elsif Is_Array_Type (Etype (E))
           and then Ekind (E) in Formal_Kind
           and then not Is_Static_Array_Type (Etype (E))
         then EW_Split (Etype (E))
         else Use_Ty);
      Why_Name : constant W_Identifier_Id :=
        To_Why_Id (E => E, Typ => Typ);
      Local_Name : constant W_Identifier_Id :=
        To_Why_Id (E => E, Typ => Typ, Local => True);
      Decl : constant W_Declaration_Id :=
        New_Type_Decl
          (Name  => To_Ident (WNE_Type),
           Alias => Typ);

      Var : constant Item_Type := Mk_Item_Of_Entity (E, Why_Name);

   --  Start of Translate_Variable

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining a ref holding the value of variable "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an alias for the name of the object's type, based on the
      --  name of the object. This is useful when generating logic functions
      --  from Ada functions, to generate additional parameters for the global
      --  objects read.

      Emit (File.Cur_Theory, Decl);

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Labels      => Name_Id_Sets.Empty_Set,
            Ref_Type => New_Named_Type (To_Ident (WNE_Type))));
      case Var.Kind is
         when UCArray =>
            for D in 1 .. Var.Dim loop
               declare
                  Ty_First : constant W_Type_Id :=
                    Get_Typ (Var.Bounds (D).First);
                  Ty_Last : constant W_Type_Id :=
                    Get_Typ (Var.Bounds (D).Last);
               begin
                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        =>
                          Attr_Append
                            (Local_Name,
                             Attribute_First,
                             D,
                             Ty_First),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Name_Id_Sets.Empty_Set,
                        Return_Type => Ty_First));
                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Labels      => Name_Id_Sets.Empty_Set,
                        Name        =>
                          Attr_Append
                            (Local_Name,
                             Attribute_Last,
                             D,
                             Ty_Last),
                        Binders     => (1 .. 0 => <>),
                        Return_Type => Ty_Last));
               end;
            end loop;
         when Regular =>
            null;
      end case;
      Insert_Item (E, Var);

      Close_Theory (File,
                    Kind           => Definition_Theory,
                    Defined_Entity => E);
   end Translate_Variable;

   -----------------------
   -- Use_Why_Base_Type --
   -----------------------

   function Use_Why_Base_Type (E : Entity_Id) return Boolean
   is
      Ty : constant Entity_Id := Etype (E);
   begin
      return not Is_Mutable_In_Why (E) and then
        Is_Scalar_Type (Ty) and then
        not Is_Boolean_Type (Ty);
   end Use_Why_Base_Type;

end Gnat2Why.Decls;
