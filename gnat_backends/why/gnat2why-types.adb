------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - T Y P E S                         --
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

--  For debugging, to print info on the output before raising an exception
with Ada.Text_IO;

with GNAT.Source_Info;

with Atree;              use Atree;
with Einfo;              use Einfo;
with Namet;              use Namet;
with Sem_Eval;           use Sem_Eval;
with Sinfo;              use Sinfo;
with Sinput;             use Sinput;
with Stand;              use Stand;

with Alfa.Definition;    use Alfa.Definition;
with Alfa.Util;          use Alfa.Util;

with Why;                use Why;
with Why.Conversions;    use Why.Conversions;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Gen.Binders;    use Why.Gen.Binders;
with Why.Gen.Decl;       use Why.Gen.Decl;
with Why.Gen.Names;      use Why.Gen.Names;
with Why.Gen.Records;    use Why.Gen.Records;
with Why.Gen.Scalars;    use Why.Gen.Scalars;
with Why.Sinfo;          use Why.Sinfo;
with Why.Types;          use Why.Types;

with Gnat2Why.Decls;     use Gnat2Why.Decls;
with Gnat2Why.Nodes;     use Gnat2Why.Nodes;

package body Gnat2Why.Types is

   procedure Declare_Ada_Abstract_Signed_Int_From_Range
     (Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id;
      Rng     : Node_Id;
      Modulus : W_Integer_Constant_Id := Why_Empty);
   --  Same as Declare_Ada_Abstract_Signed_Int but extract range information
   --  from node.

   procedure Declare_Ada_Real_From_Range
     (Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id;
      Rng     : Node_Id);
   --  Same as Declare_Ada_Real but extract range information
   --  from node.

   ------------------------------------------------
   -- Declare_Ada_Abstract_Signed_Int_From_Range --
   ------------------------------------------------

   procedure Declare_Ada_Abstract_Signed_Int_From_Range
     (Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id;
      Rng     : Node_Id;
      Modulus : W_Integer_Constant_Id := Why_Empty)
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
      Declare_Ada_Abstract_Signed_Int
        (Theory, E, First, Last, Modulus);
   end Declare_Ada_Abstract_Signed_Int_From_Range;

   ---------------------------------
   -- Declare_Ada_Real_From_Range --
   ---------------------------------

   procedure Declare_Ada_Real_From_Range
     (Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id;
      Rng     : Node_Id)
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
      Declare_Ada_Real (Theory, E, First, Last);
   end Declare_Ada_Real_From_Range;

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

      --  Standard.Boolean is modeled as bool; any other boolean subtype
      --  is modeled as an abstract type to have range checks.

      if Ty = Standard_Boolean then
         return New_Base_Type (Base_Type => EW_Bool);
      elsif Ty = Universal_Fixed then
         return New_Base_Type (Base_Type => EW_Real);
      elsif Ekind (Ty) in Private_Kind then

         --  For a private type or record subtype, use the most underlying type
         --  if it is in Alfa. Otherwise, return the special private type.

         if Type_In_Formal_Container (Ty) then
            return New_Base_Type (Base_Type => EW_Abstract, Ada_Node => Ty);
         elsif In_Alfa (Most_Underlying_Type (Ty)) then
            return Why_Logic_Type_Of_Ada_Type (Most_Underlying_Type (Ty));
         else
            return New_Base_Type (Base_Type => EW_Private);
         end if;
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
            Declare_Ada_Abstract_Signed_Int_From_Range (Theory, E, E);

         elsif Type_Based_On_Formal_Container (E) then
            Emit
              (File.Cur_Theory,
               New_Type (Name  => New_Identifier (Name => "t"),
                         Alias => Why_Logic_Type_Of_Ada_Type
                           (Underlying_Formal_Container_Type (E))));

         else
            case Ekind (E) is
            when E_Signed_Integer_Type    |
                 E_Signed_Integer_Subtype |
                 E_Enumeration_Type       |
                 E_Enumeration_Subtype    =>
               Declare_Ada_Abstract_Signed_Int_From_Range
                 (Theory, E, Scalar_Range (E));

            when Modular_Integer_Kind =>
               Declare_Ada_Abstract_Signed_Int_From_Range
                 (Theory,
                  E,
                  Scalar_Range (E),
                  New_Integer_Constant (Value => Modulus (E)));

            when Real_Kind =>
               Declare_Ada_Real_From_Range (Theory, E, Scalar_Range (E));

            when Array_Kind =>
               Declare_Ada_Array (Theory, E);

            when E_Record_Type | E_Record_Subtype =>
               Declare_Ada_Record (File, Theory, E);

            --  No private type or record subtype should be translated

            when Private_Kind =>
               raise Program_Error;

            when others =>
               Ada.Text_IO.Put_Line ("[Translate_Underlying_Type] ekind ="
                                     & Entity_Kind'Image (Ekind (E)));
               raise Not_Implemented;
            end case;
         end if;
      end Translate_Underlying_Type;

      Name : constant String := Full_Name (E);

   --  Start of Translate_Type

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for axiomatizing type "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Translate_Underlying_Type (File.Cur_Theory, E);

      --  We declare a default value for all types, in principle.
      --  Cloned subtypes are a special case, they do not need such a
      --  definition.

      if E /= Standard_Boolean and then
        E /= Universal_Fixed and then
        not Is_Scalar_Type (E) and then
        (if Ekind (E) = E_Record_Subtype then
           not (Present (Cloned_Subtype (E))))
      then
         Emit
           (File.Cur_Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Ident (WNE_Dummy),
               Binders     => (1 .. 0 => <>),
               Return_Type =>
                 New_Abstract_Type (Name => To_Why_Id (E, Local => True))));
      end if;

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
                  not Is_Primitive and then Is_Mutable_In_Why (N);
   begin
      return Why_Prog_Type_Of_Ada_Type (Etype (N), Mutable);
   end  Why_Prog_Type_Of_Ada_Obj;

end Gnat2Why.Types;
