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

with Ada.Containers.Hashed_Maps;
with Atree;              use Atree;
with Common_Containers;  use Common_Containers;
with Sinfo;              use Sinfo;
with SPARK_Util;         use SPARK_Util;
with Stand;              use Stand;
with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;

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
   procedure Init_Array_Modules;
   procedure Init_BV_Modules;
   procedure Init_BV_Conv_Modules;

   package Ada_To_Why is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Why_Node_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Entity_Modules : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Axiom_Modules  : Ada_To_Why.Map := Ada_To_Why.Empty_Map;

   --------------
   -- E_Module --
   --------------

   function E_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Cursor := Entity_Modules.Find (E);
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
            Entity_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Module;

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
      Init_Array_Modules;
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
   end Initialize;

   ------------------------
   -- Init_Array_Modules --
   ------------------------

   procedure Init_Array_Modules is
      M : constant array (1 .. 4) of W_Module_Id :=
        (1 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__1")),
         2 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__2")),
         3 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__3")),
         4 =>
           New_Module
             (File => Gnatprove_Standard_File,
              Name => NID ("Array__4")));
   begin
      for I in 1 .. 4 loop
         M_Arrays (I).Module := M (I);
         M_Arrays (I).Ty :=
           New_Type (Type_Kind  => EW_Builtin,
                     Name       => New_Name (Symbol => NID ("map"),
                                             Module => M (I)),
                     Is_Mutable => False);
         M_Arrays (I).Get :=
           New_Identifier (Module => M (I),
                           Domain => EW_Term,
                           Symbol => NID ("get"),
                           Typ    => EW_Unit_Type);
         M_Arrays (I).Set :=
           New_Identifier (Module => M (I),
                           Domain => EW_Term,
                           Symbol => NID ("set"),
                           Typ    => M_Arrays (I).Ty);
         M_Arrays (I).Bool_Eq :=
           New_Identifier (Module => M (I),
                           Domain => EW_Term,
                           Symbol => NID ("bool_eq"),
                           Typ    => EW_Bool_Type);
         M_Arrays (I).Slide :=
           New_Identifier (Module => M (I),
                           Domain => EW_Term,
                           Symbol => NID ("slide"),
                           Typ    => M_Arrays (I).Ty);
      end loop;
      M_Array_1.Module := M (1);
      M_Array_1.Concat :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("concat"),
                        Typ    => M_Arrays (1).Ty);
      M_Array_1.Compare :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("compare"),
                        Typ    => EW_Int_Type);
      M_Array_1.Xorb :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("xorb"),
                        Typ    => M_Arrays (1).Ty);
      M_Array_1.Andb :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("andb"),
                        Typ    => M_Arrays (1).Ty);
      M_Array_1.Orb :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("orb"),
                        Typ    => M_Arrays (1).Ty);
      M_Array_1.Notb :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("notb"),
                        Typ    => M_Arrays (1).Ty);
      M_Array_1.Singleton :=
        New_Identifier (Module => M (1),
                        Domain => EW_Term,
                        Symbol => NID ("singleton"),
                        Typ    => M_Arrays (1).Ty);
   end Init_Array_Modules;

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
                    Name => NID ("BitVector8"));
      M_BVs (BV16).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector16"));
      M_BVs (BV32).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector32"));
      M_BVs (BV64).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector64"));
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
                           Symbol => NID ("lsl"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsr :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("lsr"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Asr :=
           New_Identifier (Domain => EW_Term,
                           Symbol => NID ("asr"),
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
                           Symbol => NID ("to_int"),
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

      M_Main.Havoc_Fun :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symbol => NID ("__havoc"),
                        Typ    => EW_Unit_Type);

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
