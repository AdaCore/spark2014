------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - A T R E E - M O D U L E S                   --
--                                                                          --
--                                 B o d Y                                  --
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

with Ada.Containers;     use Ada.Containers;
with Atree;              use Atree;
with Common_Containers;  use Common_Containers;
with Einfo;              use Einfo;
with GNATCOLL.Utils;     use GNATCOLL.Utils;
with Gnat2Why.Util;      use Gnat2Why.Util;
with Sem_Util;           use Sem_Util;
with Sinfo;              use Sinfo;
with SPARK_Util;         use SPARK_Util;
with Stand;              use Stand;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Arrays;     use Why.Gen.Arrays;
with Why.Inter;          use Why.Inter;

package body Why.Atree.Modules is

   --  procedures to initialize the various modules
   procedure Init_Main_Module;
   procedure Init_Integer_Module;
   procedure Init_Int_Power_Module;
   procedure Init_Int_Abs_Module;
   procedure Init_Int_Div_Module;
   procedure Init_Int_Minmax_Module;
   procedure Init_Floating_Module;
   procedure Init_Boolean_Module;
   procedure Init_BV_Modules;
   procedure Init_BV_Conv_Modules;

   procedure Insert_Why_Symbols (E : Entity_Id);
   --  For the type entity E, add all the Why symbols which can be used for
   --  that type in Why to the symbol map
   --  @param E the entity for which symbols should be created

   package Ada_To_Why is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Why_Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   type Why_Symb is record
      Entity : Entity_Id;
      Symb   : Why_Name_Enum;
   end record;

   function Hash (Key : Why_Symb) return Ada.Containers.Hash_Type
   is (3 * Ada.Containers.Hash_Type (Key.Entity) +
         5 * Ada.Containers.Hash_Type (Why_Name_Enum'Pos (Key.Symb)));

   package Why_Symb_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Why_Symb,
      Element_Type    => W_Identifier_Id,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Why_Symb_Map : Why_Symb_Maps.Map := Why_Symb_Maps.Empty_Map;
   Entity_Modules : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Axiom_Modules  : Ada_To_Why.Map := Ada_To_Why.Empty_Map;

   --------------
   -- E_Module --
   --------------

   function E_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      E2 : constant Entity_Id :=
        (if Nkind (E) in N_Entity then Unique_Entity (E) else E);
      C  : constant Cursor := Entity_Modules.Find (E2);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Name,
                 Name     => NID (Full_Name (E)));
         begin
            Entity_Modules.Insert (E2, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Module;

   ------------
   -- E_Symb --
   ------------

   function E_Symb (E : Entity_Id;
                    S : Why_Name_Enum) return W_Identifier_Id
   is
      use Why_Symb_Maps;
      E2 : constant Entity_Id :=
        (if Is_Type (E) then Retysp (E) else E);
      Key : constant Why_Symb :=  Why_Symb'(Entity => E2, Symb => S);
      C : constant Cursor := Why_Symb_Map.Find (Key);
   begin
      if Has_Element (C) then
         return Element (C);
      else
         Insert_Why_Symbols (E2);
         return Why_Symb_Map.Element (Key);
      end if;
   end E_Symb;

   --------------------
   -- E_Axiom_Module --
   --------------------

   function E_Axiom_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Cursor := Axiom_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Name,
                 Name     => NID (Full_Name (E) & "__axiom"));
         begin
            Axiom_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;

   end E_Axiom_Module;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin

      --  initialize files first

      Int_File := NID ("int");
      Real_File := NID ("real");
      Ref_File := NID ("ref");
      Gnatprove_Standard_File := NID ("_gnatprove_standard");
      Ada_Model_File := NID ("ada__model");

      --  modules of the Why standard library

      Int_Module := New_Module (File => Int_File, Name => NID ("Int"));
      RealInfix := New_Module (File => Real_File, Name => NID ("RealInfix"));
      Ref_Module := New_Module (File => Ref_File, Name => NID ("Ref"));

      --  builtin Why types

      EW_Bool_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("bool")),
                  Is_Mutable => False);
      EW_Int_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("int")),
                  Is_Mutable => False);
      EW_Prop_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("prop")),
                  Is_Mutable => False);
      EW_Real_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("real")),
                  Is_Mutable => False);
      EW_Unit_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("unit")),
                  Is_Mutable => False);

      Init_Main_Module;
      Init_Integer_Module;
      Init_Int_Power_Module;
      Init_Int_Div_Module;
      Init_Int_Abs_Module;
      Init_Int_Minmax_Module;
      Init_Floating_Module;
      Init_Boolean_Module;
      Init_BV_Modules;
      Init_BV_Conv_Modules;

      --  modules of "ada__model" file

      Static_Modular_lt8 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_lt8"));
      Static_Modular_lt16 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_lt16"));
      Static_Modular_lt32 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_lt32"));
      Static_Modular_lt64 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_lt64"));
      Static_Modular_8 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_8"));
      Static_Modular_16 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_16"));
      Static_Modular_32 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_32"));
      Static_Modular_64 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_64"));
      Static_Discrete :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Discrete"));
      Dynamic_Modular :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular"));
      Dynamic_Discrete :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Discrete"));
      Static_Fixed_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Fixed_Point"));
      Dynamic_Fixed_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Fixed_Point"));
      Static_Floating_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Floating_Point"));
      Dynamic_Floating_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Floating_Point"));

      Constr_Arrays :=
        (1 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array")),
         2 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array_2")),
         3 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array_3")),
         4 => New_Module (File => Ada_Model_File,
                          Name => NID ("Constr_Array_4")));
      Unconstr_Arrays :=
        (1 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array")),
         2 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array_2")),
         3 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array_3")),
         4 => New_Module (File => Ada_Model_File,
                          Name => NID ("Unconstr_Array_4")));

      Array_Int_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Array_Int_Rep_Comparison_Axiom"));

      Array_BV8_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Array_BV8_Rep_Comparison_Axiom"));

      Array_BV16_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Array_BV16_Rep_Comparison_Axiom"));

      Array_BV32_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Array_BV32_Rep_Comparison_Axiom"));

      Array_BV64_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Array_BV64_Rep_Comparison_Axiom"));

      Standard_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Standard_Array_Logical_Op_Axioms"));

      Subtype_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Subtype_Array_Logical_Op_Axioms"));

      --  builtin unary minus

      Int_Unary_Minus :=
        New_Identifier (Domain => EW_Term,
                        Symbol => NID ("-"),
                        Typ    => EW_Int_Type);
      Fixed_Unary_Minus :=
        New_Identifier (Domain => EW_Term,
                        Symbol => NID ("-"),
                        Typ    => M_Main.Fixed_Type);
      Real_Unary_Minus :=
        New_Identifier (Domain => EW_Term,
                        Symbol => NID ("-."),
                        Typ    => EW_Real_Type);

      --  builtin infix operations

      Why_Eq :=
        New_Identifier (Domain => EW_Term,
                        Symbol => NID ("="),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Why_Neq :=
        New_Identifier (Domain => EW_Term,
                        Symbol => NID ("<>"),
                        Typ    => EW_Bool_Type,
                        Infix  => True);

      Int_Infix_Add :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("+"),
                        Typ    => EW_Int_Type,
                        Infix  => True);
      Int_Infix_Subtr :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("-"),
                        Typ    => EW_Int_Type,
                        Infix  => True);
      Int_Infix_Mult :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("*"),
                        Typ    => EW_Int_Type,
                        Infix  => True);
      Int_Infix_Le :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("<="),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Int_Infix_Lt :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("<"),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Int_Infix_Ge :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID (">="),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Int_Infix_Gt :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID (">"),
                        Typ    => EW_Bool_Type,
                        Infix  => True);

      Fixed_Infix_Add :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("+"),
                        Typ    => M_Main.Fixed_Type,
                        Infix  => True);
      Fixed_Infix_Subtr :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("-"),
                        Typ    => M_Main.Fixed_Type,
                        Infix  => True);
      Fixed_Infix_Mult :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("*"),
                        Typ    => M_Main.Fixed_Type,
                        Infix  => True);

      Real_Infix_Add :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID ("+."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Subtr :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID ("-."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Mult :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID ("*."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Le :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID ("<=."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Lt :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID ("<."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Ge :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID (">=."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Gt :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symbol => NID (">."),
                        Typ    => EW_Real_Type,
                        Infix  => True);

      --  To_String function

      To_String_Id :=
        New_Identifier (Ada_Node => Standard_String,
                        Domain   => EW_Term,
                        Module   => E_Module (Standard_String),
                        Symbol   => NID ("to_string"));

      Of_String_Id :=
        New_Identifier (Ada_Node => Standard_String,
                        Domain   => EW_Term,
                        Module   => E_Module (Standard_String),
                        Symbol   => NID ("from_string"));

      --  Other identifiers

      Old_Tag := NID ("old");
      Def_Name :=
        New_Identifier
          (Symbol => NID ("def"),
           Domain => EW_Term);

      --  modules of _gnatprove_standard file

      Array_Modules :=
        (1 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("Array__1")),
         2 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("Array__2")),
         3 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("Array__3")),
         4 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("Array__4")));
   end Initialize;

   ------------------------
   -- Init_Array_Modules --
   ------------------------

   function Init_Array_Module (Module : W_Module_Id) return M_Array_Type
   is
      M_Array : M_Array_Type;
      Ty : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("map"),
                                          Module => Module),
                  Is_Mutable => False);
   begin
      M_Array.Module := Module;

      M_Array.Ty := Ty;
      M_Array.Get :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("get"),
                        Typ    => EW_Unit_Type);
      M_Array.Set :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("set"),
                        Typ    => Ty);
      M_Array.Bool_Eq :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Array.Slide :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("slide"),
                        Typ    => Ty);

      return M_Array;
   end Init_Array_Module;

   function Init_Array_1_Module (Module : W_Module_Id) return M_Array_1_Type
   is
      M_Array_1 : M_Array_1_Type;
      Ty : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("map"),
                                          Module => Module),
                  Is_Mutable => False);
   begin

      M_Array_1.Module := Module;
      M_Array_1.Concat :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("concat"),
                        Typ    => Ty);
      M_Array_1.Singleton :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("singleton"),
                        Typ    => Ty);

      return M_Array_1;
   end Init_Array_1_Module;

   function Init_Array_1_Comp_Module (Module : W_Module_Id)
                                      return M_Array_1_Comp_Type
   is
      M_Array_1 : M_Array_1_Comp_Type;
   begin

      M_Array_1.Module := Module;
      M_Array_1.Compare :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("compare"),
                        Typ    => EW_Int_Type);

      return M_Array_1;
   end Init_Array_1_Comp_Module;

   function Init_Array_1_Bool_Op_Module (Module : W_Module_Id)
                                      return M_Array_1_Bool_Op_Type
   is
      M_Array_1 : M_Array_1_Bool_Op_Type;
      Ty : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("map"),
                                          Module => Module),
                  Is_Mutable => False);
   begin

      M_Array_1.Module := Module;
      M_Array_1.Xorb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("xorb"),
                        Typ    => Ty);
      M_Array_1.Andb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("andb"),
                        Typ    => Ty);
      M_Array_1.Orb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("orb"),
                        Typ    => Ty);
      M_Array_1.Notb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symbol => NID ("notb"),
                        Typ    => Ty);

      return M_Array_1;
   end Init_Array_1_Bool_Op_Module;

   -------------------------
   -- Init_Boolean_Module --
   -------------------------

   procedure Init_Boolean_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Boolean"));
   begin
      M_Boolean.Module := M;
      M_Boolean.Bool_Eq :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Ne :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Le :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Lt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Ge :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Gt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Notb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("notb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Andb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("andb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Notb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("notb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Orb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("orb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Xorb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("xorb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.To_Int :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("to_int"),
                        Typ    => EW_Int_Type);
      M_Boolean.Of_Int :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("of_int"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Range_Check :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("range_check_"),
                        Typ    => EW_Int_Type);
      M_Boolean.Check_Not_First :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("check_not_first"),
                        Typ    => EW_Int_Type);
      M_Boolean.Check_Not_Last :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("check_not_last"),
                        Typ    => EW_Int_Type);
      M_Boolean.First :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("first"),
                        Typ    => EW_Int_Type);
      M_Boolean.Last :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("last"),
                        Typ    => EW_Int_Type);
      M_Boolean.Range_Pred :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("in_range"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Dynamic_Prop :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("dynamic_property"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Image :=
        New_Identifier
          (Symbol => NID ("attr__ATTRIBUTE_IMAGE"),
           Module => M,
           Domain => EW_Term,
           Typ    => M_Main.String_Image_Type);
      M_Boolean.Value :=
        New_Identifier
          (Symbol => NID ("attr__ATTRIBUTE_VALUE"),
           Module => M,
           Domain => EW_Term,
           Typ    => EW_Bool_Type);
   end Init_Boolean_Module;

   --------------------------
   -- Init_BV_Conv_Modules --
   --------------------------

   procedure Init_BV_Conv_Modules is
      M : W_Module_Id;
   begin
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("BVConv_32_64"));
      M_BV_Conv_32_64 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toBig"),
                                          Typ => EW_BitVector_64_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toSmall"),
                                          Typ => EW_BitVector_32_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("range_check_"),
                                          Typ => EW_BitVector_64_Type));
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("BVConv_16_64"));
      M_BV_Conv_16_64 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toBig"),
                                          Typ => EW_BitVector_64_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toSmall"),
                                          Typ => EW_BitVector_16_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("range_check_"),
                                          Typ => EW_BitVector_64_Type));
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("BVConv_8_64"));
      M_BV_Conv_8_64 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toBig"),
                                          Typ => EW_BitVector_64_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toSmall"),
                                          Typ => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("range_check_"),
                                          Typ => EW_BitVector_64_Type));
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("BVConv_16_32"));
      M_BV_Conv_16_32 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toBig"),
                                          Typ => EW_BitVector_32_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toSmall"),
                                          Typ => EW_BitVector_16_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("range_check_"),
                                          Typ => EW_BitVector_32_Type));
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("BVConv_8_32"));
      M_BV_Conv_8_32 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toBig"),
                                          Typ => EW_BitVector_32_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toSmall"),
                                          Typ => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("range_check_"),
                                          Typ => EW_BitVector_32_Type));
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => NID ("BVConv_8_16"));
      M_BV_Conv_8_16 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toBig"),
                                          Typ => EW_BitVector_16_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("toSmall"),
                                          Typ => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symbol => NID ("range_check_"),
                                          Typ => EW_BitVector_16_Type));

   end Init_BV_Conv_Modules;

   ---------------------
   -- Init_BV_Modules --
   ---------------------

   procedure Init_BV_Modules is
   begin
      M_BVs (BV8).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BV8"));
      M_BVs (BV16).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BV16"));
      M_BVs (BV32).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BV32"));
      M_BVs (BV64).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BV64"));
      for BV in BV_Kind loop
         M_BVs (BV).T :=
           New_Type (Type_Kind  => EW_Builtin,
                     Name       => New_Name (Symbol => NID ("t"),
                                             Module => M_BVs (BV).Module),
                     Is_Mutable => False);
         M_BVs (BV).Ult :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("ult"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Ule :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("ule"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Ugt :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("ugt"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Uge :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("uge"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).BV_Min :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bv_min"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BV_Max :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bv_max"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Bool_Eq :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bool_eq"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Ne :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bool_ne"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Le :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bool_le"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Lt :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bool_lt"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Ge :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bool_ge"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Gt :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bool_gt"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).One :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("one"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Add :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("add"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Sub :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("sub"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Neg :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("neg"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Mult :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("mul"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Power :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("power"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Udiv :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("udiv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Urem :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("urem"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Urem :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("urem"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_And :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bw_and"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Or :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bw_or"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Xor :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bw_xor"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Not :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("bw_not"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BV_Abs :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("abs"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsl :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("lsl_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsr :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("lsr_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Asr :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("asr_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Rotate_Left :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("rotate_left"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Rotate_Right :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("rotate_right"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Of_Int :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("of_int"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).To_Int :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("to_uint"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Int_Type);
         M_BVs (BV).Two_Power_Size :=
           New_Identifier (Module => M_BVs (BV).Module,
                           Domain => EW_Term,
                           Symbol => NID ("two_power_size"),
                           Typ => EW_Int_Type);
      end loop;
      EW_BitVector_8_Type := M_BVs (BV8).T;
      EW_BitVector_16_Type := M_BVs (BV16).T;
      EW_BitVector_32_Type := M_BVs (BV32).T;
      EW_BitVector_64_Type := M_BVs (BV64).T;
   end Init_BV_Modules;

   --------------------------
   -- Init_Floating_Module --
   --------------------------

   procedure Init_Floating_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Floating"));
   begin
      M_Floating.Module := M;
      M_Floating.Div_Real :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("div_real"));
      M_Floating.Abs_Real :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("AbsReal.abs"));
      M_Floating.Ceil :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("ceil"));
      M_Floating.Floor :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("floor"));
      M_Floating.Power :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("power"));
      M_Floating.Real_Of_Int :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("real_of_int"));
      M_Floating.Round :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("round"));
      M_Floating.Truncate :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("truncate"));
      M_Floating.Max :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("real_max"));
      M_Floating.Min :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("real_min"));
      M_Floating.Round_Single :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("round_single"));
      M_Floating.Round_Double :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("round_double"));
      M_Floating.Bool_Eq :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Floating.Bool_Ne :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_neq"),
                        Typ    => EW_Bool_Type);
      M_Floating.Bool_Le :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      M_Floating.Bool_Lt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      M_Floating.Bool_Ge :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      M_Floating.Bool_Gt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);
   end Init_Floating_Module;

   -------------------------
   -- Init_Int_Abs_Module --
   -------------------------

   procedure Init_Int_Abs_Module is
      M : constant W_Module_Id :=
                New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Abs"));
   begin
      M_Int_Abs.Module := M;
      M_Int_Abs.Abs_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("abs"),
                        Typ    => EW_Int_Type);
   end Init_Int_Abs_Module;

   -------------------------
   -- Init_Int_Div_Module --
   -------------------------

   procedure Init_Int_Div_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Division"));
   begin
      M_Int_Div.Module := M;
      M_Int_Div.Div :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("div"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Euclid :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("euclid_div"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Rem_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("rem"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Mod_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("mod"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Math_Mod :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("math_mod"),
                        Typ    => EW_Int_Type);
   end Init_Int_Div_Module;

   ----------------------------
   -- Init_Int_Minmax_Module --
   ----------------------------

   procedure Init_Int_Minmax_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Minmax"));

   begin
      M_Int_Minmax.Module := M;
      M_Int_Minmax.Max :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("int_max"),
                        Typ    => EW_Int_Type);
      M_Int_Minmax.Min :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("int_min"),
                        Typ    => EW_Int_Type);
   end Init_Int_Minmax_Module;

   -------------------------
   -- Init_Integer_Module --
   -------------------------

   procedure Init_Integer_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Integer"));
   begin
      M_Integer.Module := M;
      M_Integer.Bool_Eq :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Ne :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Le :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Lt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Ge :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Gt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);
   end Init_Integer_Module;

   ---------------------------
   -- Init_Int_Power_Module --
   ---------------------------

   procedure Init_Int_Power_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Power"));
   begin
      M_Int_Power.Module := M;
      M_Int_Power.Power :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("power"),
                        Typ    => EW_Int_Type);
   end Init_Int_Power_Module;

   ----------------------
   -- Init_Main_Module --
   ----------------------

   procedure Init_Main_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Main"));
   begin
      M_Main.Module := M;
      M_Main.String_Image_Type :=
        New_Type (Type_Kind  => EW_Abstract,
                  Name       =>
                    New_Name (Symbol => NID ("__image"), Module => M),
                  Is_Mutable => False);

      M_Main.Type_Of_Heap :=
        New_Type (Type_Kind  => EW_Abstract,
                  Name       => New_Name (Symbol => NID ("__type_of_heap"),
                                          Module => M),
                  Is_Mutable => False);
      M_Main.Fixed_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       =>
                    New_Name (Symbol => NID ("__fixed"), Module => M),
                  Is_Mutable => False);
      M_Main.Private_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       =>
                    New_Name (Symbol => NID ("__private"), Module => M),
                  Is_Mutable => False);

      M_Main.Return_Exc :=
        New_Name (Symbol => NID ("Return__exc"));

      M_Main.Ignore_Id :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("___ignore"),
                        Typ    => EW_Unit_Type);
      M_Main.Null_Extension :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("__null_ext__"),
                        Typ    => M_Main.Private_Type);
      EW_Fixed_Type := M_Main.Fixed_Type;
      EW_Private_Type := M_Main.Private_Type;
   end Init_Main_Module;

   -------------------------
   -- Insert_Extra_Module --
   -------------------------

   procedure Insert_Extra_Module (N : Node_Id; M : W_Module_Id) is
   begin
      Entity_Modules.Insert (N, Why_Node_Id (M));
   end Insert_Extra_Module;

   ------------------------
   -- Insert_Why_Symbols --
   ------------------------

   procedure Insert_Why_Symbols (E : Entity_Id) is

      procedure Insert_Symbol (E : Entity_Id;
                               W : Why_Name_Enum;
                               I : W_Identifier_Id);
      --  For the key (E, W), add the symbol I to the symbol map
      --  @param E the entity part of the key
      --  @param W the symbol part of the key
      --  @param I the identifier to be added

      procedure Insert_Type_Symbols (E : Entity_Id)
        with Pre => Is_Type (E);
      --  add the symbols in the case E is a type
      --  @param E a type entity

      procedure Insert_Object_Symbols (E : Entity_Id)
        with Pre => Is_Object (E);
      --  add the symbols in the case E is a object
      --  @param E an object entity

      -------------------
      -- Insert_Symbol --
      -------------------

      procedure Insert_Symbol (E : Entity_Id;
                               W : Why_Name_Enum;
                               I : W_Identifier_Id) is
      begin
         Why_Symb_Map.Insert (Why_Symb'(E, W), I);
      end Insert_Symbol;

      ---------------------------
      -- Insert_Object_Symbols --
      ---------------------------

      procedure Insert_Object_Symbols (E : Entity_Id) is
         M  : constant W_Module_Id := E_Module (E);
      begin
         Insert_Symbol
           (E, WNE_Attr_Address,
            New_Identifier
              (Symbol => NID ("attr__ATTRIBUTE_ADDRESS"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));
      end Insert_Object_Symbols;

      -------------------------
      -- Insert_Type_Symbols --
      -------------------------

      procedure Insert_Type_Symbols (E : Entity_Id) is
         M  : constant W_Module_Id := E_Module (E);
         Ty : constant W_Type_Id := EW_Abstract (E);
      begin

         Insert_Symbol
           (E, WNE_Bool_Eq,
            New_Identifier
              (Symbol => NID ("bool_eq"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Bool_Type));

         Insert_Symbol
           (E, WNE_Dummy,
            New_Identifier
              (Symbol => NID ("dummy"),
               Module => M,
               Domain => EW_Term,
               Typ    => Ty));

      --  symbols for scalar types

         if Is_Scalar_Type (E) then
            declare
               Base : constant W_Type_Id :=
                 Get_EW_Term_Type (E);
            begin
               Insert_Symbol
                 (E, WNE_Attr_Image,
                  New_Identifier
                    (Symbol => NID ("attr__ATTRIBUTE_IMAGE"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => M_Main.String_Image_Type));
               Insert_Symbol
                 (E, WNE_Attr_Value,
                  New_Identifier
                    (Symbol => NID ("attr__ATTRIBUTE_VALUE"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Check_Not_First,
                  New_Identifier
                    (Symbol => NID ("check_not_first"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Check_Not_Last,
                  New_Identifier
                    (Symbol => NID ("check_not_last"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Range_Check_Fun,
                  New_Identifier
                    (Symbol => NID ("range_check_"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Dynamic_Property,
                  New_Identifier
                    (Symbol => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));
               Insert_Symbol
                 (E, WNE_To_Rep,
                  New_Identifier
                    (Module => M,
                     Domain => EW_Term,
                     Symbol => NID ("to_rep"),
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Of_Rep,
                  New_Identifier
                    (Module => M,
                     Domain => EW_Term,
                     Symbol => NID ("of_rep"),
                     Typ    => Ty));

               --  symbols for static scalar types

               if not Type_Is_Modeled_As_Base (E) then
                  Insert_Symbol
                    (E, WNE_Attr_First,
                     New_Identifier
                       (Symbol => NID ("first"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));
                  Insert_Symbol
                    (E, WNE_Attr_Last,
                     New_Identifier
                       (Symbol => NID ("last"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));
                  Insert_Symbol
                    (E, WNE_Range_Pred,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("in_range"),
                        Typ    => EW_Bool_Type));
               end if;

               --  symbols for modular types

               if Has_Modular_Integer_Type (E) then
                  declare
                     To_Int : constant W_Identifier_Id :=
                       New_Identifier
                         (Symbol => NID ("to_int"),
                          Module => M,
                          Domain => EW_Term,
                          Typ    => EW_Int_Type);
                  begin
                     Insert_Symbol (E, WNE_To_Int, To_Int);
                     Insert_Symbol (E, WNE_To_BitVector, To_Int);
                     Insert_Symbol
                       (E, WNE_Of_BitVector,
                        New_Identifier
                          (Symbol => NID ("of_int"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => Base));
                     Insert_Symbol
                       (E, WNE_Dynamic_Property_BV_Int,
                        New_Identifier
                          (Symbol => NID ("dynamic_property_int"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                     Insert_Symbol
                       (E, WNE_Attr_Modulus,
                        New_Identifier
                          (Symbol => NID ("attr__ATTRIBUTE_MODULUS"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => Base));
                     Insert_Symbol
                       (E, WNE_Range_Check_Fun_BV_Int,
                        New_Identifier
                          (Symbol => NID ("range_check_int_"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                  end;
               end if;

               --  symbols for modular static types

               if Has_Modular_Integer_Type (E)
                 and then not Type_Is_Modeled_As_Base (E)
               then
                  Insert_Symbol
                    (E, WNE_Range_Pred_BV_Int,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("in_range_int"),
                        Typ    => EW_Bool_Type));
               end if;

               --  symbols for fixed point types

               if Is_Fixed_Point_Type (E) then
                  Insert_Symbol
                    (E, WNE_Attr_Small,
                     New_Identifier
                       (Symbol => NID ("inv_small"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));
                  Insert_Symbol
                    (E, WNE_To_Fixed,
                     New_Identifier
                       (Symbol => NID ("to_fixed"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Fixed_Type));
                  Insert_Symbol
                    (E, WNE_Of_Fixed,
                     New_Identifier
                       (Symbol => NID ("of_fixed"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Ty));
                  Insert_Symbol
                    (E, WNE_To_Int,
                     New_Identifier
                       (Symbol => NID ("to_int"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E, WNE_Of_Int,
                     New_Identifier
                       (Symbol => NID ("of_int"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));
                  Insert_Symbol
                    (E, WNE_Fixed_Point_Mult,
                     New_Identifier
                       (Symbol => NID ("fxp_mult"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Fixed_Type));
                  Insert_Symbol
                    (E, WNE_Fixed_Point_Mult_Int,
                     New_Identifier
                       (Symbol => NID ("fxp_mult_int"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Fixed_Type));
                  Insert_Symbol
                    (E, WNE_Fixed_Point_Div,
                     New_Identifier
                       (Symbol => NID ("fxp_div"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Fixed_Type));
                  Insert_Symbol
                    (E, WNE_Fixed_Point_Div_Int,
                     New_Identifier
                       (Symbol => NID ("fxp_div_int"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Fixed_Type));
                  Insert_Symbol
                    (E, WNE_Fixed_Point_Div_Result_Int,
                     New_Identifier
                       (Symbol => NID ("fxp_div_result_int"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E, WNE_To_Real,
                     New_Identifier
                       (Symbol => NID ("to_real"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Real_Type));
                  Insert_Symbol
                    (E, WNE_Of_Real,
                     New_Identifier
                       (Symbol => NID ("of_real"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Fixed_Type));
               end if;
               if Is_Floating_Point_Type (E) then
                  Insert_Symbol
                    (E, WNE_To_Real,
                     New_Identifier
                       (Symbol => NID ("to_real"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Real_Type));
                  Insert_Symbol
                    (E, WNE_Of_Real,
                     New_Identifier
                       (Symbol => NID ("of_real"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Ty));
                  Insert_Symbol
                    (E, WNE_Float_Round_Tmp,
                     New_Identifier
                       (Symbol => NID ("round_real_tmp"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Real_Type));
                  Insert_Symbol
                    (E, WNE_Float_Round,
                     New_Identifier
                       (Symbol => NID ("round_real"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Real_Type));
                  Insert_Symbol
                    (E, WNE_Float_Pred,
                     New_Identifier
                       (Symbol => NID ("prev_representable"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Real_Type));
                  Insert_Symbol
                    (E, WNE_Float_Succ,
                     New_Identifier
                       (Symbol => NID ("next_representable"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Real_Type));
               end if;
            end;

            --  symbols for record types

         elsif Is_Record_Type (E)
           or else Full_View_Not_In_SPARK (E)
         then
            declare
               Root    : constant Entity_Id :=
                 Root_Record_Type (E);
               Root_Ty : constant W_Type_Id :=
                 New_Named_Type (To_Why_Type (Root));
            begin
               Insert_Symbol
                 (E, WNE_Attr_Value_Size,
                  New_Identifier
                    (Symbol => NID ("value__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Object_Size,
                  New_Identifier
                    (Symbol => NID ("object__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Range_Check_Fun,
                  New_Identifier
                    (Symbol => NID ("range_check_"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Root_Ty));
               Insert_Symbol
                 (E, WNE_Range_Pred,
                  New_Identifier
                    (Module => M,
                     Domain => EW_Term,
                     Symbol => NID ("in_range"),
                     Typ    => EW_Bool_Type));
               Insert_Symbol
                 (E, WNE_To_Base,
                  New_Identifier
                    (Symbol => NID ("to_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Root_Ty));
               Insert_Symbol
                 (E, WNE_Of_Base,
                  New_Identifier
                    (Symbol => NID ("of_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty));
               Insert_Symbol
                 (E, WNE_Rec_Main,
                  New_Identifier
                    (Symbol => NID ("rec__main__"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Private_Type));
               Insert_Symbol
                 (E, WNE_Rec_Split_Discrs,
                  New_Identifier
                    (Symbol => NID (To_String (WNE_Rec_Split_Discrs)),
                     Module => M,
                     Domain => EW_Term));
               Insert_Symbol
                 (E, WNE_Rec_Split_Fields,
                  New_Identifier
                    (Symbol => NID (To_String (WNE_Rec_Split_Fields)),
                     Module => M,
                     Domain => EW_Term));

               if Is_Tagged_Type (E) then
                  Insert_Symbol
                    (E, WNE_Dispatch_Eq,
                     New_Identifier
                       (Symbol => NID ("__dispatch_eq"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));
                  Insert_Symbol
                    (E, WNE_Attr_Tag,
                     New_Identifier
                       (Symbol => NID ("attr__tag"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E, WNE_Tag,
                     New_Identifier
                       (Symbol => NID ("__tag"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E, WNE_Rec_Extension,
                     New_Identifier
                       (Symbol => NID ("rec__ext__"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Private_Type));
               end if;

               if Has_Private_Ancestor_Or_Root (E) then
                  Insert_Symbol
                    (E, WNE_Rec_Ancestor,
                     New_Identifier
                       (Symbol => NID ("rec__anc__"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Private_Type));
                  Insert_Symbol
                    (E, WNE_Hide_Ancestor,
                     New_Identifier
                       (Symbol => NID ("hide_anc__"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Private_Type));
               end if;

               if (not Is_Constrained (E)
                   and then Has_Defaulted_Discriminants (E))
                 --  ???
                 or else
                   (not Is_Constrained (Root)
                    and then Has_Defaulted_Discriminants (Root))
               then
                  Insert_Symbol
                    (E, WNE_Attr_Constrained,
                     New_Identifier
                       (Symbol => NID ("attr__constrained"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));
               end if;
            end;

            --  symbols for array types

         elsif Is_Array_Type (E) then
            declare
               Ar_Dim : constant Positive := Positive (Number_Dimensions (E));
            begin
               Insert_Symbol
                 (E, WNE_Attr_Value_Size,
                  New_Identifier
                    (Symbol => NID ("value__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Object_Size,
                  New_Identifier
                    (Symbol => NID ("object__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Dynamic_Property,
                  New_Identifier
                    (Symbol => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));
               Insert_Symbol
                 (E, WNE_To_Array,
                  New_Identifier
                    (Symbol => NID ("to_array"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Get_Array_Theory (E).Ty));
               Insert_Symbol
                 (E, WNE_Of_Array,
                  New_Identifier
                    (Symbol => NID ("of_array"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty));
               Insert_Symbol
                 (E, WNE_Array_Elts,
                  New_Identifier
                    (Symbol => NID ("elts"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Get_Array_Theory (E).Ty));
               if Ar_Dim = 1 and then
                 Is_Discrete_Type (Component_Type (E))
               then
                  Insert_Symbol
                    (E, WNE_To_Rep,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symbol => NID ("to_rep"),
                        Typ    => EW_Abstract (Component_Type (E))));
               end if;
               for Dim in 1 .. Ar_Dim loop
                  declare
                     First_Str : constant String :=
                       (if Dim = 1 then "first"
                        else "first_" & Image (Dim, 1));
                     Last_Str  : constant String :=
                       (if Dim = 1 then "last" else "last_" & Image (Dim, 1));
                     Length_Str : constant String :=
                       (if Dim = 1 then "length"
                        else "length_" & Image (Dim, 1));
                     Int_Str : constant String :=
                       (if Dim = 1 then "to_int"
                        else "to_int_" & Image (Dim, 1));
                     Base_Range_Str : constant String :=
                       (if Dim = 1 then "in_range_base"
                        else "in_range_base_" & Image (Dim, 1));
                     Index_Str : constant String :=
                       (if Dim = 1 then "index_dynamic_property"
                        else "index_dynamic_property_" & Image (Dim, 1));
                  begin
                     Insert_Symbol
                       (E, WNE_Attr_First (Dim),
                        New_Identifier
                          (Symbol => NID (First_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_Attr_Last (Dim),
                        New_Identifier
                          (Symbol => NID (Last_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_Attr_Length (Dim),
                        New_Identifier
                          (Symbol => NID (Length_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_To_Int (Dim),
                        New_Identifier
                          (Symbol => NID (Int_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_Array_Base_Range_Pred (Dim),
                        New_Identifier
                          (Symbol => NID (Base_Range_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                     Insert_Symbol
                       (E, WNE_Index_Dynamic_Property (Dim),
                        New_Identifier
                          (Symbol => NID (Index_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                  end;
               end loop;
            end;
         end if;

      end Insert_Type_Symbols;

      --  beginning of processing for Insert_Why_Symbols

   begin
      if Is_Type (E) then
         Insert_Type_Symbols (E);
      elsif Is_Object (E) then
         Insert_Object_Symbols (E);
      end if;
   end Insert_Why_Symbols;

   ------------
   -- MF_BVs --
   ------------

   function MF_BVs (T : W_Type_Id) return M_BV_Type is
   begin
      if T = EW_BitVector_8_Type then
         return M_BVs (BV8);
      elsif T = EW_BitVector_16_Type then
         return M_BVs (BV16);
      elsif T = EW_BitVector_32_Type then
         return M_BVs (BV32);
      elsif T = EW_BitVector_64_Type then
         return M_BVs (BV64);
      else
         raise Program_Error;
      end if;
   end MF_BVs;

end Why.Atree.Modules;
