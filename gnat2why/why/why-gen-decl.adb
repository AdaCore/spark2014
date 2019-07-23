------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        W H Y - G E N - D E C L                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
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

with Ada.Containers.Indefinite_Ordered_Maps;
with Common_Containers;   use Common_Containers;
with GNATCOLL.Symbols;    use GNATCOLL.Symbols;
with GNATCOLL.Utils;      use GNATCOLL.Utils;
with Types;               use Types;
with VC_Kinds;            use VC_Kinds;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Images;          use Why.Images;
with Why.Inter;           use Why.Inter;
with Why.Sinfo;           use Why.Sinfo;
with Why.Types;           use Why.Types;

package body Why.Gen.Decl is

   procedure Emit_Record_Projection_Declaration
     (Section       : W_Section_Id;
      Param_Ty_Name : W_Name_Id;
      Field_Id      : W_Identifier_Id;
      Labels        : Symbol_Sets.Set)
   with Pre => Field_Id /= Why_Empty;
   --  Emit declaration of a projection for a Why3 record type. The projection
   --  projects values of the record type to given field of this type.
   --  The declaration consists of a declaration of a function that returns a
   --  value of a field Field_Id of a value of the type Param_Ty_Name and
   --  declaration projection metas (see Emit_Projection_Metas).
   --  @param Section the section where the projection declaration will be
   --      emitted.
   --  @param Param_Ty_Name the name of the record type being projected.
   --  @param Field_Id the identifier of the field to that the record is
   --      projected. Its type is the type to that the record type is projected
   --      (and must be different from Why_Empty).
   --  @param Labels the counterexample labels for the record field.

   ----------
   -- Emit --
   ----------

   procedure Emit
     (Theory : W_Theory_Declaration_Id;
      Decl   : W_Declaration_Id) is
   begin
      Theory_Declaration_Append_To_Declarations
        (Id => Theory,
         New_Item => +Decl);
   end Emit;

   ----------
   -- Emit --
   ----------

   procedure Emit
     (S    : W_Section_Id;
      Decl : W_Declaration_Id) is
   begin
      Emit (Why_Sections (S).Cur_Theory, Decl);
   end Emit;

   ---------------------------
   -- Emit_Projection_Metas --
   ---------------------------

   procedure Emit_Projection_Metas
     (Section : W_Section_Id; Projection_Fun : String) is
   begin
      --  mark function as projection function
      Emit (Section,
            New_Meta_Declaration (Name      => NID (Model_Proj_Meta),
                                  Parameter => NID ("function " &
                                      Projection_Fun)));

      --  disable inlining of projection functions
      Emit (Section,
            New_Meta_Declaration (Name      => NID ("inline:no"),
                                  Parameter => NID ("function " &
                                      Projection_Fun)));
   end Emit_Projection_Metas;

   -----------------------------
   -- Emit_Record_Declaration --
   -----------------------------

   procedure Emit_Record_Declaration
     (Section      : W_Section_Id;
      Name         : W_Name_Id;
      Binders      : Why.Gen.Binders.Binder_Array;
      SPARK_Record : Boolean := False)
   is
   begin
      --  Emit declaration of the record
      Emit (Section,
            Decl   => New_Record_Definition (Name     => Name,
                                             Binders  => Binders));

      --  For each record field, emit projection from the record to the field
      for Binder in Binders'Range loop
         Emit_Record_Projection_Declaration
           (Section       => Section,
            Param_Ty_Name => Name,
            Field_Id      => Binders (Binder).B_Name,
            Labels        =>
              (if SPARK_Record then Binders (Binder).Labels
               else Symbol_Sets.Empty_Set));
      end loop;
   end Emit_Record_Declaration;

   package Projection_Names is new Ada.Containers.Indefinite_Ordered_Maps
     (Key_Type     => String,
      Element_Type => Positive,
      "<"          => Standard."<",
      "="          => Standard."=");

   Projection_Names_Decls : Projection_Names.Map;
   --  Map from the name of projection to the number of declarations of
   --  projections with this name.
   --  The name of the projection is composed from the name of the type that
   --  is projected and if the projection projects SPARK record type to a field
   --  of the record also from the spark field name. That is, the name of the
   --  projection is not unique.
   --  The name of the projection function must be unique and it is composed
   --  of the name of the projection and if there are more declarations
   --  of projections with the same name, the name of projection function is
   --  also composed of the number of declarations of  projections with this
   --  name.

   ----------------------------------------
   -- Emit_Record_Projection_Declaration --
   ----------------------------------------

   procedure Emit_Record_Projection_Declaration
     (Section       : W_Section_Id;
      Param_Ty_Name : W_Name_Id;
      Field_Id      : W_Identifier_Id;
      Labels        : Symbol_Sets.Set)
   is
      use Projection_Names;

      --  Projection function name
      Param_Ty_Name_Str : constant String := Img (Get_Symb (Param_Ty_Name));

      Proj_Name : constant String :=
        Param_Ty_Name_Str & "_" & Img (Get_Symb (Get_Name (Field_Id)));

      Proj_Name_Cursor : constant Cursor :=
        Projection_Names_Decls.Find (Proj_Name);

      Proj_Name_Decls_Num : constant Positive :=
        (if Proj_Name_Cursor = No_Element then 1
         else Element (Proj_Name_Cursor));

      Proj_Fun_Name : constant String :=
        Proj_Name
        & (if Proj_Name_Decls_Num = 1
           then ""
           else "__" & Image (Proj_Name_Decls_Num, 1))
        & "__projection";

      --  Parameter type and identifier
      Param_Ty    : constant W_Type_Id :=
        New_Named_Type (Name => Param_Ty_Name);
      Param_Ident : constant W_Identifier_Id :=
        Why.Gen.Names.New_Identifier (Name => "a", Typ => Param_Ty);

      --  The access to the field to that the record is projected
      Field_Access : constant W_Expr_Id :=
        Why.Atree.Builders.New_Record_Access
          (Name  => +Param_Ident,
           Field => Field_Id);

   begin
      --  Update number of declarations of projection with name Proj_Name
      if Proj_Name_Cursor = No_Element then
         Projection_Names_Decls.Insert (Proj_Name, 2);
      else
         Projection_Names_Decls (Proj_Name) := Proj_Name_Decls_Num + 1;
      end if;

      Emit
        (Section,
         Why.Atree.Builders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => Why.Gen.Names.New_Identifier (
              Name => Proj_Fun_Name),
            Binders     => (1 => New_Binder (Domain => EW_Prog,
                                             Name => Param_Ident,
                                             Arg_Type => Param_Ty)),
            Return_Type => Get_Type (+Field_Id),
            Labels      => Labels,
            Location    => No_Location,
            Def         => Field_Access));

      Emit_Projection_Metas (Section, Proj_Fun_Name);
   end Emit_Record_Projection_Declaration;

   ------------------------------
   -- Emit_Ref_Type_Definition --
   ------------------------------

   procedure Emit_Ref_Type_Definition
     (File : W_Section_Id;
      Name : W_Name_Id)
   is
      Field_Typ : constant W_Type_Id := New_Type
        (Type_Kind  => EW_Abstract,
         Name       => Name);
   begin
      Emit_Record_Declaration
        (Section => File,
         Name    => Ref_Append (Name),
         Binders => (1 => (B_Name  => Content_Append (Name, Field_Typ),
                           Mutable => True,
                           others  => <>)));
   end Emit_Ref_Type_Definition;

   ---------------------------
   -- New_Havoc_Declaration --
   ---------------------------

   function New_Havoc_Declaration (Name : W_Name_Id) return W_Declaration_Id
   is
      Typ       : constant W_Type_Id := New_Type
        (Type_Kind  => EW_Abstract,
         Name       => Ref_Append (Name));
      Havoc_Fun : constant W_Identifier_Id :=
        Havoc_Append (Name);
      X         : constant W_Identifier_Id :=
        New_Identifier (Domain => EW_Prog,
                        Name   => "x",
                        Typ    => Typ);
   begin
      return Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Havoc_Fun,
                  Binders     => (1 => New_Binder (Domain   => EW_Prog,
                                                   Name     => X,
                                                   Arg_Type => Typ)),
                  Effects     => New_Effects (Writes   => (1 => X)),
                  Return_Type => EW_Unit_Type,
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location);
   end New_Havoc_Declaration;

   -------------------
   -- New_Type_Decl --
   -------------------

   function New_Type_Decl (Name : String) return W_Declaration_Id is
   begin
      return
        New_Type_Decl
          (Name   => New_Name (Symb => NID (Name)),
           Labels => Symbol_Sets.Empty_Set);
   end New_Type_Decl;

   function New_Type_Decl
     (Name  : W_Name_Id;
      Alias : W_Type_Id) return W_Declaration_Id is
   begin
      return New_Type_Decl
        (Name       => Name,
         Labels     => Symbol_Sets.Empty_Set,
         Definition => New_Transparent_Type_Definition
           (Domain          => EW_Prog,
            Type_Definition => Alias));
   end New_Type_Decl;

end Why.Gen.Decl;
