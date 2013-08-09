------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - S C A L A R S                       --
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

with Snames;             use Snames;

with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Inter;          use Why.Inter;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

package body Why.Gen.Scalars is

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId);
   --  Define the attributes first, last, modulus for the given type.

   -------------------------------------
   -- Declare_Ada_Abstract_Signed_Int --
   -------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int
     (Theory  : W_Theory_Declaration_Id;
      Entity  : Entity_Id;
      First   : W_Integer_Constant_Id;
      Last    : W_Integer_Constant_Id;
      Modulus : W_Integer_Constant_Id)
   is
      Why_Id : constant W_Identifier_Id := To_Why_Id (Entity, Local => True);
      Is_Mod : constant Boolean := Modulus /= Why_Empty;
      Clone_Id : constant W_Identifier_Id :=
        (if Is_Mod then
         New_Identifier (Name    => """ada__model"".Modular")
         else
         New_Identifier (Name    => """ada__model"".Discrete"));
      Clone_Subst : constant W_Clone_Substitution_Array :=
        (1 =>
           New_Clone_Substitution
             (Kind      => EW_Type_Subst,
              Orig_Name => New_Identifier (Name => "t"),
              Image     => Why_Id),
         2 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => To_Ident (WNE_Attr_First),
              Image     => To_Ident (WNE_Attr_First)),
         3 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => To_Ident (WNE_Attr_Last),
              Image     => To_Ident (WNE_Attr_Last)));
   begin

      Emit (Theory, New_Type (Name => Why_Id));

      Define_Scalar_Attributes
        (Theory    => Theory,
         Base_Type => EW_Int,
         First     => +First,
         Last      => +Last,
         Modulus   => +Modulus);
      Emit (Theory,
            New_Clone_Declaration
              (Theory_Kind => EW_Module,
               Clone_Kind  => EW_Export,
               Origin      => Clone_Id,
               Substitutions =>
                 (if Is_Mod then
                  Clone_Subst &
                  (1 => New_Clone_Substitution
                      (Kind      => EW_Function,
                       Orig_Name => To_Ident (WNE_Attr_Modulus),
                       Image     => To_Ident (WNE_Attr_Modulus)))
                    else Clone_Subst)));
   end Declare_Ada_Abstract_Signed_Int;

   ----------------------
   -- Declare_Ada_Real --
   ----------------------

   procedure Declare_Ada_Real
     (Theory  : W_Theory_Declaration_Id;
      Entity  : Entity_Id;
      First   : W_Real_Constant_Id;
      Last    : W_Real_Constant_Id)
   is
      Why_Name : constant W_Identifier_Id := To_Why_Id (Entity, Local => True);
      Clone_Id : constant W_Identifier_Id :=
         New_Identifier (Name    => """ada__model"".Floating_Point");
      Clone_Subst : constant W_Clone_Substitution_Array :=
        (1 =>
           New_Clone_Substitution
             (Kind      => EW_Type_Subst,
              Orig_Name => New_Identifier (Name => "t"),
              Image     => Why_Name),
         2 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => To_Ident (WNE_Attr_First),
              Image     => To_Ident (WNE_Attr_First)),
         3 =>
           New_Clone_Substitution
             (Kind      => EW_Function,
              Orig_Name => To_Ident (WNE_Attr_Last),
              Image     => To_Ident (WNE_Attr_Last)));

   begin
      Emit (Theory, New_Type (Name => Why_Name));
      Define_Scalar_Attributes
        (Theory    => Theory,
         Base_Type => EW_Real,
         First     => +First,
         Last      => +Last,
         Modulus   => Why_Empty);
      Emit (Theory,
            New_Clone_Declaration
              (Theory_Kind => EW_Module,
               Clone_Kind  => EW_Export,
               Origin      => Clone_Id,
               Substitutions => Clone_Subst));
   end Declare_Ada_Real;

   ------------------------------
   -- Define_Scalar_Attributes --
   ------------------------------

   procedure Define_Scalar_Attributes
     (Theory     : W_Theory_Declaration_Id;
      Base_Type  : EW_Scalar;
      First      : W_Term_Id;
      Last       : W_Term_Id;
      Modulus    : W_Term_OId)
   is
      type Scalar_Attr is (S_First, S_Last, S_Modulus);

      type Attr_Info is record
         Attr_Id : Attribute_Id;
         Value   : W_Term_Id;
      end record;

      Attr_Values : constant array (Scalar_Attr) of Attr_Info :=
                      (S_First   => (Attribute_First, First),
                       S_Last    => (Attribute_Last, Last),
                       S_Modulus => (Attribute_Modulus, Modulus));
   begin
      for J in Attr_Values'Range loop
         declare
            Spec      : Declaration_Spec;
            Emit_Decl : Boolean;
         begin
            if Attr_Values (J).Value /= Why_Empty then
               Spec      := (Kind   => W_Function_Def,
                             Domain => EW_Term,
                             Term   => Attr_Values (J).Value,
                             others => <>);
               Emit_Decl := True;
            else
               Spec      := (Kind   => W_Function_Decl,
                             Domain => EW_Term,
                             others => <>);
               --  We do not emit the declaration for modulus if this
               --  type does not have a modulus.
               Emit_Decl := J /= S_Modulus;
            end if;
            if Emit_Decl then
               Spec.Name :=
                 To_Ident (Attr_To_Why_Name (Attr_Values (J).Attr_Id));
               Emit_Top_Level_Declarations
                 (Theory      => Theory,
                  Binders     => (1 .. 0 => <>),
                  Return_Type => New_Base_Type (Base_Type => Base_Type),
                  Spec        => (1 => Spec));
            end if;
         end;
      end loop;
   end Define_Scalar_Attributes;

end Why.Gen.Scalars;
