------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Atree;              use Atree;
with Einfo;              use Einfo;
with Gnat2Why.Decls;     use Gnat2Why.Decls;
with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with Stand;              use Stand;

with Alfa.Definition;    use Alfa.Definition;
with Alfa.Util;          use Alfa.Util;

with Why;                use Why;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Scalars;    use Why.Gen.Scalars;
with Why.Gen.Records;    use Why.Gen.Records;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

with Gnat2Why.Expr;      use Gnat2Why.Expr;

package body Gnat2Why.Types is

   function Is_Ada_Base_Type (N : Node_Id) return Boolean;
   --  Return True is N is of an Ada base type

   procedure Declare_Ada_Abstract_Signed_Int_From_Range
     (Theory  : W_Theory_Declaration_Id;
      Rng     : Node_Id;
      Is_Base : Boolean);
   --  Same as Declare_Ada_Abstract_Signed_Int but extract range information
   --  from node.

   procedure Declare_Ada_Real_From_Range
     (Theory  : W_Theory_Declaration_Id;
      Rng     : Node_Id;
      Is_Base : Boolean);
   --  Same as Declare_Ada_Real but extract range information
   --  from node.

   ------------------------------------------------
   -- Declare_Ada_Abstract_Signed_Int_From_Range --
   ------------------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int_From_Range
     (Theory  : W_Theory_Declaration_Id;
      Rng     : Node_Id;
      Is_Base : Boolean)
   is
      Range_Node : constant Node_Id := Get_Range (Rng);
      First      : W_Integer_Constant_Id := Why_Empty;
      Last       : W_Integer_Constant_Id := Why_Empty;
   begin
      if Is_Static_Expression (Low_Bound (Range_Node)) then
         First :=
           New_Integer_Constant (Value => Expr_Value (Low_Bound (Range_Node)));
      end if;
      if Is_Static_Expression (High_Bound (Range_Node)) then
         Last :=
           New_Integer_Constant (Value =>
              Expr_Value (High_Bound (Range_Node)));
      end if;
      Declare_Ada_Abstract_Signed_Int (Theory, First, Last, Is_Base);
   end Declare_Ada_Abstract_Signed_Int_From_Range;

   ---------------------------------
   -- Declare_Ada_Real_From_Range --
   ---------------------------------

   procedure Declare_Ada_Real_From_Range
     (Theory  : W_Theory_Declaration_Id;
      Rng     : Node_Id;
      Is_Base : Boolean)
   is
      Range_Node : constant Node_Id := Get_Range (Rng);
      First      : W_Real_Constant_Id := Why_Empty;
      Last       : W_Real_Constant_Id := Why_Empty;
   begin
      if Is_Static_Expression (Low_Bound (Range_Node)) then
         First :=
            New_Real_Constant (Value =>
              Expr_Value_R (Low_Bound (Range_Node)));
      end if;
      if Is_Static_Expression (High_Bound (Range_Node)) then
         Last :=
            New_Real_Constant (Value =>
              Expr_Value_R (High_Bound (Range_Node)));
      end if;
      Declare_Ada_Real (Theory, First, Last, Is_Base);
   end Declare_Ada_Real_From_Range;

   ----------------------
   -- Is_Ada_Base_Type --
   ----------------------

   function Is_Ada_Base_Type (N : Node_Id) return Boolean is
      T : constant Entity_Id := Etype (N);
   begin
      return Base_Type (T) = T;
   end Is_Ada_Base_Type;

   -------------------------------
   -- Why_Logic_Type_Of_Ada_Obj --
   -------------------------------

   function Why_Logic_Type_Of_Ada_Obj
     (N : Node_Id)
     return W_Primitive_Type_Id is
   begin
      return Why_Logic_Type_Of_Ada_Type (Etype (N));
   end  Why_Logic_Type_Of_Ada_Obj;

   --------------------------------
   -- Why_Logic_Type_Of_Ada_Type --
   --------------------------------

   function Why_Logic_Type_Of_Ada_Type
     (Ty : Node_Id)
     return W_Primitive_Type_Id is
   begin
      --  For a private type or record subtype, use the most underlying type if
      --  it is in Alfa. Otherwise, return the special private type.

      if Ekind (Ty) in Private_Kind | E_Record_Subtype then
         if In_Alfa (Most_Underlying_Type (Ty)) then
            return Why_Logic_Type_Of_Ada_Type (Most_Underlying_Type (Ty));
         else
            return New_Base_Type (Base_Type => EW_Private);
         end if;

      --  Standard.Boolean is modeled as bool; any other boolean subtype
      --  is modeled as an abstract type to have range checks.

      elsif Ty = Standard_Boolean then
         return New_Base_Type (Base_Type => EW_Bool);

      elsif Ty = Universal_Fixed then
         return New_Base_Type (Base_Type => EW_Real);
      else
         return New_Base_Type (Base_Type => EW_Abstract, Ada_Node => Ty);
      end if;
   end  Why_Logic_Type_Of_Ada_Type;

   --------------------
   -- Translate_Type --
   --------------------

   procedure Translate_Type
     (File : in out Why_File;
      E    : Entity_Id)
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
         if E = Standard_Boolean or else
           E = Universal_Fixed
         then
            null;

         elsif E = Standard_Character           or else
               E = Standard_Wide_Character      or else
               E = Standard_Wide_Wide_Character
         then
            Declare_Ada_Abstract_Signed_Int_From_Range
              (Theory, E, Is_Base => Is_Ada_Base_Type (E));

         else
            case Ekind (E) is
            when E_Signed_Integer_Type    |
                 E_Signed_Integer_Subtype |
                 E_Enumeration_Type       |
                 E_Enumeration_Subtype    =>
               Declare_Ada_Abstract_Signed_Int_From_Range
                 (Theory, Scalar_Range (E),
                  Is_Base => Is_Ada_Base_Type (E));

            when Modular_Integer_Kind =>
               Declare_Ada_Abstract_Modular
                 (Theory, Modulus (E),
                  Is_Base => Is_Ada_Base_Type (E));

            when Real_Kind =>
               Declare_Ada_Real_From_Range
                 (Theory, Scalar_Range (E),
                  Is_Base => Is_Ada_Base_Type (E));

            when Array_Kind =>
               Declare_Ada_Array (Theory, E);

            when E_Record_Type =>
               declare
                  Number_Of_Fields : Natural := 0;
                  Field            : Node_Id := First_Entity (E);
               begin
                  while Present (Field) loop
                     if Ekind (Field) in Object_Kind then
                        Number_Of_Fields := Number_Of_Fields + 1;
                     end if;

                     Next_Entity (Field);
                  end loop;

                  --  Do nothing if the record is empty.
                  --  Maybe we have to do something special here? Map all
                  --  empty records to type unit in Why?

                  if Number_Of_Fields = 0 then
                     Emit (Theory, New_Type (To_String (WNE_Type)));
                     return;
                  end if;

                  declare
                     Field   : Node_Id := First_Entity (E);
                     Binders : Binder_Array (1 .. Number_Of_Fields);
                     J       : Natural := 0;
                  begin
                     while Present (Field) loop
                        if Ekind (Field) in Object_Kind then
                           J := J + 1;
                           Binders (J) :=
                             (B_Name => To_Why_Id (Field, Local => True),
                              B_Type =>
                                Why_Logic_Type_Of_Ada_Type (Etype (Field)),
                              others => <>);
                        end if;

                        Next_Entity (Field);
                     end loop;
                     Define_Ada_Record (Theory, Binders);
                  end;
               end;

            --  No private type or record subtype should be translated

            when Private_Kind | E_Record_Subtype =>
               raise Program_Error;

            when others =>
               raise Not_Implemented;
            end case;
         end if;
      end Translate_Underlying_Type;

      Name : constant String := Full_Name (E);

   --  Start of Translate_Type

   begin
      Open_Theory (File, Name);
      Translate_Underlying_Type (File.Cur_Theory, E);

      --  If E is the full view of a private type, use its partial view as the
      --  filtering entity, as it is the entity used everywhere in AST.

      if Is_Full_View (E) then
         Close_Theory (File, Filter_Entity => Partial_View (E));
      else
         Close_Theory (File, Filter_Entity => E);
      end if;
   end Translate_Type;

   -------------------------------
   -- Why_Prog_Type_Of_Ada_Type --
   -------------------------------

   function Why_Prog_Type_Of_Ada_Type (Ty : Node_Id; Is_Mutable : Boolean)
      return W_Simple_Value_Type_Id
   is
      Base : constant W_Primitive_Type_Id :=
        Why_Logic_Type_Of_Ada_Type (Ty);
   begin
      if Is_Mutable then
         return New_Ref_Type (Ada_Node => Ty, Aliased_Type => Base);
      else
         return +Base;
      end if;
   end  Why_Prog_Type_Of_Ada_Type;

   function Why_Prog_Type_Of_Ada_Obj
     (N            : Node_Id;
      Is_Primitive : Boolean := False)
     return W_Simple_Value_Type_Id
   is
      Mutable : constant Boolean :=
                  not Is_Primitive and then Is_Mutable (N);
   begin
      return Why_Prog_Type_Of_Ada_Type (Etype (N), Mutable);
   end  Why_Prog_Type_Of_Ada_Obj;

end Gnat2Why.Types;
