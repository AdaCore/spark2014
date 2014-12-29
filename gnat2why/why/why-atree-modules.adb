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

with Atree;              use Atree;
with Sinfo;              use Sinfo;

with Why.Atree.Builders; use Why.Atree.Builders;
with Why.Gen.Names;      use Why.Gen.Names;

with Gnat2Why.Nodes;     use Gnat2Why.Nodes;

package body Why.Atree.Modules is

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
        New_Type (Type_Kind  => EW_Bool,
                  Name       => New_Name (Symbol => NID ("bool")),
                  Is_Mutable => False);
      EW_Int_Type :=
        New_Type (Type_Kind  => EW_Int,
                  Name       => New_Name (Symbol => NID ("int")),
                  Is_Mutable => False);
      EW_Fixed_Type :=
        New_Type (Type_Kind  => EW_Fixed,
                  Name       => New_Name (Symbol => NID ("__fixed")),
                  Is_Mutable => False);
      EW_Private_Type :=
        New_Type (Type_Kind  => EW_Private,
                  Name       => New_Name (Symbol => NID ("__private")),
                  Is_Mutable => False);
      EW_Prop_Type :=
        New_Type (Type_Kind  => EW_Prop,
                  Name       => New_Name (Symbol => NID ("prop")),
                  Is_Mutable => False);
      EW_Real_Type :=
        New_Type (Type_Kind  => EW_Real,
                  Name       => New_Name (Symbol => NID ("real")),
                  Is_Mutable => False);
      EW_Unit_Type :=
        New_Type (Type_Kind  => EW_Unit,
                  Name       => New_Name (Symbol => NID ("unit")),
                  Is_Mutable => False);

      Why_Types (EW_Bool) := EW_Bool_Type;
      Why_Types (EW_Int) := EW_Int_Type;
      Why_Types (EW_Fixed) := EW_Fixed_Type;
      Why_Types (EW_Private) := EW_Private_Type;
      Why_Types (EW_Prop) := EW_Prop_Type;
      Why_Types (EW_Real) := EW_Real_Type;
      Why_Types (EW_Unit) := EW_Unit_Type;

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
      Int_Bit_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => NID ("Int_Bitwise"));
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

      Static_Modular :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Static_Modular"));
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

      Array_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Array_Comparison_Axiom"));

      Standard_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Standard_Array_Logical_Op_Axioms"));

      Subtype_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => NID ("Subtype_Array_Logical_Op_Axioms"));

      --  identifiers of Integer module
      Integer_Bitwise_And :=
        New_Identifier (Module => Int_Bit_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bitwise_and"),
                        Typ    => EW_Int_Type);
      Integer_Bitwise_Or :=
        New_Identifier (Module => Int_Bit_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bitwise_or"),
                        Typ    => EW_Int_Type);
      Integer_Bitwise_Xor :=
        New_Identifier (Module => Int_Bit_Module,
                        Domain => EW_Term,
                        Symbol => NID ("bitwise_xor"),
                        Typ    => EW_Int_Type);
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

      --  Other identifiers

      Old_Tag := NID ("old");
   end Initialize;

   -------------------------
   -- Insert_Extra_Module --
   -------------------------

   procedure Insert_Extra_Module (N : Node_Id; M : W_Module_Id) is
   begin
      Entity_Modules.Insert (N, Why_Node_Id (M));
   end Insert_Extra_Module;
end Why.Atree.Modules;
