------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
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

with GNAT.Source_Info;

with Atree;               use Atree;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;
with Sinput;              use Sinput;
with Snames;              use Snames;
with String_Utils;        use String_Utils;

with SPARK_Definition;    use SPARK_Definition;
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
with Why.Gen.Records;     use Why.Gen.Records;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

package body Gnat2Why.Decls is

   Counter_Example_Label : constant String := "GP_CE_Relevant";

   function Entity_Relevant_For_Counter_Example (E : Entity_Id) return Boolean
   is (Ekind (Etype (E)) in Scalar_Kind)
   with Pre => Nkind (E) in N_Entity;
   --  Returns true if the given entity should be included in the
   --  counter-example model.

   function Mk_Item_Of_Entity
     (E    : Entity_Id) return Item_Type;

   -------------------------
   -- Mk_Item_From_Entity --
   -------------------------

   function Mk_Item_Of_Entity
     (E    : Entity_Id)
     return Item_Type
   is
      --  We first build the type that we use in Why; this may be e.g. String

      Use_Ty : constant Entity_Id :=
        (if Ekind (E) in Object_Kind and then Present (Actual_Subtype (E))
         and then Entity_In_SPARK (Actual_Subtype (E)) then
              Actual_Subtype (E) else Etype (E));
   begin
      if Entity_In_SPARK (Use_Ty)
        and then Is_Array_Type (Use_Ty)
        and then not Is_Static_Array_Type (Use_Ty)
      then
         declare
            Typ    : constant W_Type_Id := EW_Split (Use_Ty);
            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ);
            Binder : constant Binder_Type :=
              Binder_Type'(Ada_Node => E,
                           B_Name   => Name,
                           B_Ent    => null,
                           Mutable  => Is_Mutable_In_Why (E));
            Result : Item_Type :=
              (Kind    => UCArray,
               Content => Binder,
               Dim     => Natural (Number_Dimensions (Etype (E))),
               Bounds  => (others => <>));
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
      elsif Entity_In_SPARK (Use_Ty)
        and then Is_Record_Type (Etype (E))
      then
         declare
            Result   : Item_Type :=
              (Kind   => DRecord,
               Typ    => Use_Ty,
               others => <>);
            Unconstr : constant Boolean :=
              not Is_Constrained (Etype (E)) and then
              Has_Defaulted_Discriminants (Etype (E));
         begin
            if Count_Fields (Use_Ty) > 0 or else Is_Tagged_Type (Use_Ty) then
               Result.Fields :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'(Ada_Node => E,
                                 B_Name   =>
                                   New_Identifier
                                     (Ada_Node => E,
                                      Domain   => EW_Term,
                                      Name     =>
                                        To_String (WNE_Rec_Split_Fields),
                                      Module   => E_Module (E),
                                      Typ      =>
                                        Field_Type_For_Fields (Use_Ty)),
                                 B_Ent    => null,
                                 Mutable  => True));
            end if;

            if Number_Discriminants (Use_Ty) > 0 then
               Result.Discrs :=
                 (Present => True,
                  Binder  =>
                    Binder_Type'(Ada_Node => E,
                                 B_Name   =>
                                   New_Identifier
                                     (Ada_Node => E,
                                      Domain   => EW_Term,
                                      Name     =>
                                        To_String (WNE_Rec_Split_Discrs),
                                      Module   => E_Module (E),
                                      Typ      =>
                                        Field_Type_For_Discriminants (Use_Ty)),
                                 B_Ent    => null,
                                 Mutable  => Unconstr));
            end if;

            if Unconstr then
               Result.Constr :=
                 (Present => True,
                  Id      => New_Identifier
                    (Ada_Node => E,
                     Domain   => EW_Term,
                     Name     => To_String (WNE_Attr_Constrained),
                     Module   => E_Module (E),
                     Typ      => EW_Bool_Type));
            end if;

            if Is_Tagged_Type (Use_Ty) then
               Result.Tag :=
                 (Present => True,
                  Id      => New_Identifier
                    (Ada_Node => E,
                     Domain   => EW_Term,
                     Name     => To_String (WNE_Attr_Tag),
                     Module   => E_Module (E),
                     Typ      => EW_Int_Type));
            end if;

            return Result;
         end;
      else
         declare
            Typ    : constant W_Type_Id :=
              (if Ekind (E) = E_Abstract_State then EW_Private_Type
               elsif Ekind (E) = E_Loop_Parameter then EW_Int_Type
               else EW_Abstract (Use_Ty));
            Name   : constant W_Identifier_Id :=
              To_Why_Id (E => E, Typ => Typ);
            Binder : constant Binder_Type :=
              Binder_Type'(Ada_Node => E,
                           B_Name   => Name,
                           B_Ent    => null,
                           Mutable  => Is_Mutable_In_Why (E));
         begin
            return (Regular, Binder);
         end;
      end if;
   end Mk_Item_Of_Entity;

   ------------------------------
   -- Translate_Abstract_State --
   ------------------------------

   procedure Translate_Abstract_State
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Var      : constant Item_Type := Mk_Item_Of_Entity (E);
   begin
      Open_Theory (File, E_Module (E),
                   Comment =>
                     "Module for defining a ref holding the value "
                       & "of abstract state "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Labels   => Name_Id_Sets.Empty_Set,
            Ref_Type => EW_Private_Type));

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
      Typ    : constant W_Type_Id  := EW_Abstract (Etype (E));
      Labels : Name_Id_Sets.Set    := Name_Id_Sets.Empty_Set;
   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, E_Module (E),
                   Comment =>
                     "Module for defining the constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a "logic", whose axiom will be given in a completion

      if Entity_Relevant_For_Counter_Example (E) then
         Labels.Include (NID (Counter_Example_Label));
      end if;

      Emit (File.Cur_Theory,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Domain => EW_Term, Local => True),
               Binders     => (1 .. 0 => <>),
               Labels      => Labels,
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

      Open_Theory (File, E_Axiom_Module (E),
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
                 (Ada_Node    => E,
                  Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

         --  In the general case, we generate a defining axiom if necessary and
         --  possible.

         else
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Ada_Node    => E,
                  Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
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
        (File,
         Module =>
           New_Module (Name => NID (Capitalize_First (E.all)),
                       File => No_Name),
         Comment =>
           "Module declaring the external object """ & E.all &
           ","" created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_With_Clause (File.Cur_Theory, Ref_Module, EW_Import, EW_Module);

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E.all, Local => True),
            Labels   => Name_Id_Sets.Empty_Set,
            Ref_Type => EW_Private_Type));

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
   begin
      Open_Theory (File, E_Module (E),
                   Comment =>
                     "Module for defining the loop exit exception for the loop"
                   & """" & Get_Name_String (Chars (E)) & """"
                   & (if Sloc (E) > 0 then
                     " defined at " & Build_Location_String (Sloc (E))
                     else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (File.Cur_Theory,
            New_Exception_Declaration
              (Name => Loop_Exception_Name (E, Local => True),
               Arg  => Why_Empty));

      Close_Theory (File,
                    Kind => Standalone_Theory);
   end Translate_Loop_Entity;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Var    : constant Item_Type := Mk_Item_Of_Entity (E);
      Labels : Name_Id_Sets.Set   := Name_Id_Sets.Empty_Set;
   begin
      Open_Theory (File, E_Module (E),
                   Comment =>
                     "Module for defining a ref holding the value of variable "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      if Entity_Relevant_For_Counter_Example (E) then
         Labels.Include (NID (Counter_Example_Label));
      end if;

      case Var.Kind is
         when DRecord =>
            if Var.Fields.Present then

               --  generate a global ref for the fields

               Emit
                 (File.Cur_Theory,
                  New_Global_Ref_Declaration
                    (Name     => Remove_Prefix (Var.Fields.Binder.B_Name),
                     Labels   => Labels,
                     Ref_Type => Get_Typ (Var.Fields.Binder.B_Name)));
            end if;

            if Var.Discrs.Present then

               --  generate a global ref or constant for the fields

               if Var.Discrs.Binder.Mutable then
                  Emit
                    (File.Cur_Theory,
                     New_Global_Ref_Declaration
                       (Name     => Remove_Prefix (Var.Discrs.Binder.B_Name),
                        Labels   => Labels,
                        Ref_Type => Get_Typ (Var.Discrs.Binder.B_Name)));
               else
                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        =>
                          Remove_Prefix (Var.Discrs.Binder.B_Name),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Labels,
                        Return_Type => Get_Typ (Var.Discrs.Binder.B_Name)));
               end if;
            end if;

            if Var.Constr.Present then

               --  generate a constant for 'Constrained attribute

                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Remove_Prefix (Var.Constr.Id),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Labels,
                        Return_Type => Get_Typ (Var.Constr.Id)));
            end if;

            if Var.Tag.Present then

               --  generate a constant for 'Tag attribute

                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Remove_Prefix (Var.Tag.Id),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Labels,
                        Return_Type => Get_Typ (Var.Tag.Id)));
            end if;

         when UCArray =>

            --  generate a global ref for the content

            Emit
              (File.Cur_Theory,
               New_Global_Ref_Declaration
                 (Name     => Remove_Prefix (Var.Content.B_Name),
                  Labels   => Labels,
                  Ref_Type => Get_Typ (Var.Content.B_Name)));

            for D in 1 .. Var.Dim loop
               declare
                  Ty_First   : constant W_Type_Id :=
                    Get_Typ (Var.Bounds (D).First);
                  Ty_Last    : constant W_Type_Id :=
                    Get_Typ (Var.Bounds (D).Last);
               begin

                  --  generate constants for bounds

                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Remove_Prefix (Var.Bounds (D).First),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Labels,
                        Return_Type => Ty_First));
                  Emit
                    (File.Cur_Theory,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Remove_Prefix (Var.Bounds (D).Last),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Labels,
                        Return_Type => Ty_Last));
               end;
            end loop;
         when Regular =>

            --  generate a global ref

            Emit
              (File.Cur_Theory,
               New_Global_Ref_Declaration
                 (Name     => Remove_Prefix (Var.Main.B_Name),
                  Labels   => Labels,
                  Ref_Type => Get_Typ (Var.Main.B_Name)));
         when Func =>
            raise Program_Error;
      end case;
      Insert_Item (E, Var);

      Close_Theory (File,
                    Kind           => Definition_Theory,
                    Defined_Entity => E);
   end Translate_Variable;

   ----------------------------
   -- Use_Base_Type_For_Type --
   ----------------------------

   function Use_Base_Type_For_Type (E : Entity_Id) return Boolean
   is
   begin
      return Is_Scalar_Type (E) and then
        not Is_Boolean_Type (E);
   end Use_Base_Type_For_Type;

   -----------------------
   -- Use_Why_Base_Type --
   -----------------------

   function Use_Why_Base_Type (E : Entity_Id) return Boolean is
      Ty : constant Entity_Id := Etype (E);
   begin
      return not Is_Mutable_In_Why (E) and then
        Use_Base_Type_For_Type (Ty);
   end Use_Why_Base_Type;

end Gnat2Why.Decls;
