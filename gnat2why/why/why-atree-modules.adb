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
      BitVector_8_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector8"));
      BitVector_16_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector16"));
      BitVector_32_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector32"));
      BitVector_64_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BitVector64"));
      BVConv_32_64_Module  :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BVConv_32_64"));
      BVConv_16_64_Module  :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BVConv_16_64"));
      BVConv_8_64_Module  :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BVConv_8_64"));
      BVConv_16_32_Module  :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BVConv_16_32"));
      BVConv_8_32_Module  :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BVConv_8_32"));
      BVConv_8_16_Module  :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("BVConv_8_16"));

      --  builtin Why types

      EW_Bool_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("bool")),
                  Is_Mutable => False);
      EW_Int_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("int")),
                  Is_Mutable => False);
      EW_Fixed_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("__fixed")),
                  Is_Mutable => False);
      EW_Private_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("__private")),
                  Is_Mutable => False);
      EW_Prop_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("prop")),
                  Is_Mutable => False);
      EW_Real_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("real")),
                  Is_Mutable => False);
      EW_BitVector_8_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("t"),
                                          Module => BitVector_8_Module),
                  Is_Mutable => False);
      EW_BitVector_16_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("t"),
                                         Module => BitVector_16_Module),
                  Is_Mutable => False);
      EW_BitVector_32_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("t"),
                                         Module => BitVector_32_Module),
                  Is_Mutable => False);
      EW_BitVector_64_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("t"),
                                         Module => BitVector_64_Module),
                  Is_Mutable => False);
      EW_Unit_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symbol => NID ("unit")),
                  Is_Mutable => False);

      --  modules of "_gnatprove_standard.mlw" file

      Main_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Main"));
      Integer_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Integer"));
      Int_Power_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Power"));
      Int_Div_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Division"));
      Int_Minmax_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Minmax"));
      Int_Abs_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Abs"));
      Floating_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Floating"));
      Boolean_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => NID ("Boolean"));

      Array_Modules :=
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

      --  modules of "ada__model" file

      Static_Modular_Default :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular_Default"));
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
      Dynamic_Modular_lt8 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_lt8"));
      Dynamic_Modular_lt16 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_lt16"));
      Dynamic_Modular_lt32 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_lt32"));
      Dynamic_Modular_lt64 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_lt64"));
      Dynamic_Modular_8 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_8"));
      Dynamic_Modular_16 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_16"));
      Dynamic_Modular_32 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_32"));
      Dynamic_Modular_64 :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Dynamic_Modular_64"));
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
                        Typ    => EW_Fixed_Type);
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
                        Typ    => EW_Fixed_Type,
                        Infix  => True);
      Fixed_Infix_Subtr :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("-"),
                        Typ    => EW_Fixed_Type,
                        Infix  => True);
      Fixed_Infix_Mult :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symbol => NID ("*"),
                        Typ    => EW_Fixed_Type,
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

      --  identifiers of Integer module
      Integer_Div :=
        New_Identifier (Module => Int_Div_Module,
                        Domain => EW_Term,
                        Symbol => NID ("div"),
                        Typ    => EW_Int_Type);
      Euclid_Div :=
        New_Identifier (Module => Int_Div_Module,
                        Domain => EW_Term,
                        Symbol => NID ("euclid_div"),
                        Typ    => EW_Int_Type);
      Integer_Rem :=
        New_Identifier (Module => Int_Div_Module,
                        Domain => EW_Term,
                        Symbol => NID ("rem"),
                        Typ    => EW_Int_Type);
      Integer_Mod :=
        New_Identifier (Module => Int_Div_Module,
                        Domain => EW_Term,
                        Symbol => NID ("mod"),
                        Typ    => EW_Int_Type);
      Integer_Power :=
        New_Identifier (Module => Int_Power_Module,
                        Domain => EW_Term,
                        Symbol => NID ("power"),
                        Typ    => EW_Int_Type);
      Integer_Math_Mod :=
        New_Identifier (Module => Int_Div_Module,
                        Domain => EW_Term,
                        Symbol => NID ("math_mod"),
                        Typ    => EW_Int_Type);
      Integer_Max :=
        New_Identifier (Module => Int_Minmax_Module,
                        Domain => EW_Term,
                        Symbol => NID ("int_max"),
                        Typ    => EW_Int_Type);
      Integer_Min :=
        New_Identifier (Module => Int_Minmax_Module,
                        Domain => EW_Term,
                        Symbol => NID ("int_min"),
                        Typ    => EW_Int_Type);
      Integer_Abs :=
        New_Identifier (Module => Int_Abs_Module,
                        Domain => EW_Term,
                        Symbol => NID ("abs"),
                        Typ    => EW_Int_Type);

      Int_Bool_Eq :=
        New_Identifier (Module => Integer_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      Int_Bool_Ne :=
        New_Identifier (Module => Integer_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      Int_Bool_Le :=
        New_Identifier (Module => Integer_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      Int_Bool_Lt :=
        New_Identifier (Module => Integer_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      Int_Bool_Ge :=
        New_Identifier (Module => Integer_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      Int_Bool_Gt :=
        New_Identifier (Module => Integer_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);

   --  Identifiers of the Main module

      String_Image_Type :=
        New_Type (Type_Kind  => EW_Abstract,
                  Name       =>
                    New_Name (Symbol => NID ("__image")),
                  Is_Mutable => False);

      Type_Of_Heap :=
        New_Type (Type_Kind  => EW_Abstract,
                  Name       => New_Name (Symbol => NID ("__type_of_heap")),
                  Is_Mutable => False);

      Return_Exc :=
        New_Name (Symbol => NID ("Return__exc"));

      Havoc_Fun :=
        New_Identifier (Domain => EW_Term,
                        Module => Main_Module,
                        Symbol => NID ("__havoc"),
                        Typ    => EW_Unit_Type);

      Ignore_Id :=
        New_Identifier (Domain => EW_Term,
                        Module => Main_Module,
                        Symbol => NID ("___ignore"),
                        Typ    => EW_Unit_Type);

      Bool_Not :=
        New_Identifier (Domain => EW_Term,
                        Module => Main_Module,
                        Symbol => NID ("notb"),
                        Typ    => EW_Bool_Type);

      --  identifiers of the "_gnatprove_standard.Floating" module

      Floating_Div_Real :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("div_real"));
      Floating_Abs_Real :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("AbsReal.abs"));
      Floating_Ceil :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("ceil"));
      Floating_Floor :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("floor"));
      Floating_Power :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("power"));
      Floating_Real_Of_Int :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("real_of_int"));
      Floating_Round :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("round"));
      Floating_Truncate :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("truncate"));
      Floating_Max :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("real_max"));
      Floating_Min :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("real_min"));
      Floating_Round_Single :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("round_single"));
      Floating_Round_Double :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("round_double"));

      Real_Bool_Eq :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      Real_Bool_Ne :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      Real_Bool_Le :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      Real_Bool_Lt :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      Real_Bool_Ge :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      Real_Bool_Gt :=
        New_Identifier (Module => Floating_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);

      Bool_Bool_Eq :=
        New_Identifier (Module => Boolean_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      Bool_Bool_Ne :=
        New_Identifier (Module => Boolean_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      Bool_Bool_Le :=
        New_Identifier (Module => Boolean_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      Bool_Bool_Lt :=
        New_Identifier (Module => Boolean_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      Bool_Bool_Ge :=
        New_Identifier (Module => Boolean_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      Bool_Bool_Gt :=
        New_Identifier (Module => Boolean_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);

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

   --------------------------------------
   -- Modular Identifiers Constructors --
   --------------------------------------

   function Create_Modular_Operator
     (Typ    : W_Type_Id;
      Symbol : Name_Id) return W_Identifier_Id is
   begin
      return New_Identifier (Module =>
                               (if Typ = EW_BitVector_8_Type then
                                   BitVector_8_Module
                                elsif Typ = EW_BitVector_16_Type then
                                   BitVector_16_Module
                                elsif Typ = EW_BitVector_32_Type then
                                   BitVector_32_Module
                                elsif Typ = EW_BitVector_64_Type then
                                   BitVector_64_Module
                                else raise Program_Error),
                             Domain => EW_Term,
                             Symbol => Symbol,
                             Typ => Typ);
   end Create_Modular_Operator;

   function Create_Modular_Rem (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("urem"));
   end Create_Modular_Rem;

   function Create_Modular_Div (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("udiv"));
   end Create_Modular_Div;

   function Create_Modular_Mul (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("mul"));
   end Create_Modular_Mul;

   function Create_Modular_Add (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("add"));
   end Create_Modular_Add;

   function Create_Modular_Sub (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("sub"));
   end Create_Modular_Sub;

   function Create_Modular_Neg (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("neg"));
   end Create_Modular_Neg;

   function Create_Modular_And (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bw_and"));
   end Create_Modular_And;

   function Create_Modular_Or  (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bw_or"));
   end Create_Modular_Or;

   function Create_Modular_Xor (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bw_xor"));
   end Create_Modular_Xor;

   function Create_Modular_Not (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bw_not"));
   end Create_Modular_Not;

   function Create_Modular_Ge (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("uge"));
   end Create_Modular_Ge;

   function Create_Modular_Gt (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("ugt"));
   end Create_Modular_Gt;

   function Create_Modular_Le (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("ule"));
   end Create_Modular_Le;

   function Create_Modular_Lt (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("ult"));
   end Create_Modular_Lt;

   function Create_Modular_Bool_Ge (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bool_ge"));
   end Create_Modular_Bool_Ge;

   function Create_Modular_Bool_Gt (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bool_gt"));
   end Create_Modular_Bool_Gt;

   function Create_Modular_Bool_Le (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bool_le"));
   end Create_Modular_Bool_Le;

   function Create_Modular_Bool_Lt (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bool_lt"));
   end Create_Modular_Bool_Lt;

   function Create_Modular_Bool_Eq (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bool_eq"));
   end Create_Modular_Bool_Eq;

   function Create_Modular_Bool_Neq (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("bool_ne"));
   end Create_Modular_Bool_Neq;

   function Create_Modular_Abs (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("abs"));
   end Create_Modular_Abs;

   function Create_Modular_Power (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("power"));
   end Create_Modular_Power;

   function Create_Modular_Lsl (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("lsl"));
   end Create_Modular_Lsl;

   function Create_Modular_Lsr (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("lsr"));
   end Create_Modular_Lsr;

   function Create_Modular_Asr (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("asr"));
   end Create_Modular_Asr;

   function Create_Modular_Rl (Typ : W_Type_Id)
                                   return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("rotate_left"));
   end Create_Modular_Rl;

   function Create_Modular_Rr (Typ : W_Type_Id)
                                   return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("rotate_right"));
   end Create_Modular_Rr;

   function Create_Modular_ToInt (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("to_int"));
   end Create_Modular_ToInt;

   function Create_Modular_OfInt (Typ : W_Type_Id) return W_Identifier_Id is
   begin
      return Create_Modular_Operator (Typ, NID ("of_int"));
   end Create_Modular_OfInt;

   function Create_Modular_Modulus (Typ : W_Type_Id) return W_Identifier_Id
   is
      Symbol : constant Name_Id := NID ("two_power_size");
   begin
      return (if Typ = EW_BitVector_8_Type then
                 New_Identifier (Module => BitVector_8_Module,
                                 Domain => EW_Term,
                                 Symbol => Symbol,
                                 Typ => EW_Int_Type)
              elsif Typ = EW_BitVector_16_Type then
                 New_Identifier (Module => BitVector_16_Module,
                                 Domain => EW_Term,
                                 Symbol => Symbol,
                                 Typ => EW_Int_Type)
              elsif Typ = EW_BitVector_32_Type then
                 New_Identifier (Module => BitVector_32_Module,
                                 Domain => EW_Term,
                                 Symbol => Symbol,
                                 Typ => EW_Int_Type)
              elsif Typ = EW_BitVector_64_Type then
                 New_Identifier (Module => BitVector_64_Module,
                                 Domain => EW_Term,
                                 Symbol => Symbol,
                                 Typ => EW_Int_Type)
              else raise Program_Error);
   end Create_Modular_Modulus;

   function Create_Modular_Converter
     (From, To : W_Type_Id) return W_Identifier_Id
   is
      Module : W_Module_Id;
      Symbol : Name_Id;
   begin
      if From = EW_BitVector_8_Type then

         Symbol := NID ("toBig");

         if To = EW_BitVector_16_Type then
            Module := BVConv_8_16_Module;
         elsif To = EW_BitVector_32_Type then
            Module := BVConv_8_32_Module;
         elsif To = EW_BitVector_64_Type then
            Module := BVConv_8_64_Module;
         else
            raise Program_Error;
         end if;

      elsif From = EW_BitVector_16_Type then

         if To = EW_BitVector_8_Type then
            Module := BVConv_8_16_Module;
            Symbol := NID ("toSmall");
         elsif To = EW_BitVector_32_Type then
            Module := BVConv_16_32_Module;
            Symbol := NID ("toBig");
         elsif To = EW_BitVector_64_Type then
            Module := BVConv_16_64_Module;
            Symbol := NID ("toBig");
         else
            raise Program_Error;
         end if;

      elsif From = EW_BitVector_32_Type then

         if To = EW_BitVector_8_Type then
            Module := BVConv_8_32_Module;
            Symbol := NID ("toSmall");
         elsif To = EW_BitVector_16_Type then
            Module := BVConv_16_32_Module;
            Symbol := NID ("toSmall");
         elsif To = EW_BitVector_64_Type then
            Module := BVConv_32_64_Module;
            Symbol := NID ("toBig");
         else
            raise Program_Error;
         end if;

      elsif From = EW_BitVector_64_Type then

         if To = EW_BitVector_8_Type then
            Module := BVConv_8_64_Module;
            Symbol := NID ("toSmall");
         elsif To = EW_BitVector_16_Type then
            Module := BVConv_16_64_Module;
            Symbol := NID ("toSmall");
         elsif To = EW_BitVector_32_Type then
            Module := BVConv_32_64_Module;
            Symbol := NID ("toSmall");
         else
            raise Program_Error;
         end if;

      else
         raise Program_Error;
      end if;

      return New_Identifier (Module => Module,
                             Domain => EW_Term,
                             Symbol => Symbol,
                             Typ => To);
   end Create_Modular_Converter;

   function Create_Modular_Converter_Range_Check
     (From, To : W_Type_Id) return W_Identifier_Id
   is
   begin
      return New_Identifier (Module =>
                               (if From = EW_BitVector_16_Type then
                                   --  To = EW_BitVector_8_Type
                                   BVConv_8_16_Module
                                elsif From = EW_BitVector_32_Type then
                                  (if To = EW_BitVector_8_Type then
                                        BVConv_8_32_Module
                                   else --  To = EW_BitVector_16_Type
                                      BVConv_16_32_Module)
                                else --  From = EW_BitVector_64_Type
                                  (if To = EW_BitVector_8_Type then
                                        BVConv_8_64_Module
                                   elsif To = EW_BitVector_16_Type then
                                      BVConv_16_64_Module
                                   else --  To = EW_BitVector_32_Type
                                      BVConv_32_64_Module)),
                             Domain => EW_Term,
                             Symbol => NID ("range_check_"),
                             Typ => To);
   end Create_Modular_Converter_Range_Check;

   -------------------------
   -- Insert_Extra_Module --
   -------------------------

   procedure Insert_Extra_Module (N : Node_Id; M : W_Module_Id) is
   begin
      Entity_Modules.Insert (N, Why_Node_Id (M));
   end Insert_Extra_Module;
end Why.Atree.Modules;
