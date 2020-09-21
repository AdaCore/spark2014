-----------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - A T R E E - M O D U L E S                   --
--                                                                          --
--                                 B o d Y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Characters.Handling;    use Ada.Characters.Handling;
with Ada.Containers;             use Ada.Containers;
with Ada.Strings.Unbounded;      use Ada.Strings.Unbounded;
with Common_Containers;          use Common_Containers;
with GNATCOLL.Utils;             use GNATCOLL.Utils;
with Gnat2Why.Tables;            use Gnat2Why.Tables;
with Snames;                     use Snames;
with SPARK_Atree;                use SPARK_Atree;
with SPARK_Util;                 use SPARK_Util;
with SPARK_Util.Types;           use SPARK_Util.Types;
with Stand;                      use Stand;
with String_Utils;               use String_Utils;
with VC_Kinds;                   use VC_Kinds;
with Why.Atree.Accessors;        use Why.Atree.Accessors;
with Why.Atree.Builders;         use Why.Atree.Builders;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Arrays;             use Why.Gen.Arrays;
with Why.Gen.Init;               use Why.Gen.Init;
with Why.Gen.Pointers;           use Why.Gen.Pointers;
with Why.Images;                 use Why.Images;
with Why.Inter;                  use Why.Inter;

package body Why.Atree.Modules is

   --  procedures to initialize the various modules
   procedure Init_Boolean_Module;
   procedure Init_Builtin_From_Image_Module;
   procedure Init_BV_Conv_Modules;
   procedure Init_BV_Modules;
   procedure Init_Compat_Tags_Module;
   procedure Init_Floating_Conv_Module;
   procedure Init_Floating_Module;
   procedure Init_Integer_Module;
   procedure Init_Int_Abs_Module;
   procedure Init_Int_Div_Module;
   procedure Init_Int_Minmax_Module;
   procedure Init_Int_Power_Module;
   procedure Init_Int_Gcd_Module;
   procedure Init_Labels;
   procedure Init_Main_Module;
   procedure Init_Real_Module;
   procedure Init_Real_Abs_Module;
   procedure Init_Real_From_Int_Module;
   procedure Init_Real_Minmax_Module;
   procedure Init_Real_Power_Module;
   procedure Init_Subprogram_Access_Module;

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

   Why_Symb_Map      : Why_Symb_Maps.Map := Why_Symb_Maps.Empty_Map;
   Entity_Modules    : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Axiom_Modules     : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Compl_Modules     : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Init_Modules      : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Rec_Axiom_Modules : Ada_To_Why.Map := Ada_To_Why.Empty_Map;
   Rep_Modules       : Ada_To_Why.Map := Ada_To_Why.Empty_Map;

   --------------
   -- E_Module --
   --------------

   function E_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      E2 : constant Entity_Id :=
        (if Nkind (E) in N_Entity then Unique_Entity (E) else E);
      C  : constant Ada_To_Why.Cursor := Entity_Modules.Find (E2);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Symbol,
                 Name     => Full_Name (E));
            --  ??? why New_Mode is called with E and not E2?
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

   function E_Symb
     (E            : Entity_Id;
      S            : Why_Name_Enum;
      Relaxed_Init : Boolean := False) return W_Identifier_Id
   is
      use Why_Symb_Maps;
      E2 : constant Entity_Id := (if Is_Type (E) then Retysp (E) else E);
      Key : constant Why_Symb := Why_Symb'(Entity => E2, Symb => S);
      C : constant Why_Symb_Maps.Cursor := Why_Symb_Map.Find (Key);
   begin
      return Id : W_Identifier_Id do
         if Has_Element (C) then
            Id := Element (C);
         else
            Insert_Why_Symbols (E2);
            Id := Why_Symb_Map.Element (Key);
         end if;

         if Relaxed_Init then
            Id := To_Init_Module (Id);
         end if;
      end return;
   end E_Symb;

   --------------------
   -- E_Axiom_Module --
   --------------------

   function E_Axiom_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Ada_To_Why.Cursor := Axiom_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            Name : constant String :=
              Full_Name (E) & To_String (WNE_Axiom_Suffix);
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Symbol,
                 Name     => Name);
         begin
            Axiom_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Axiom_Module;

   --------------------
   -- E_Compl_Module --
   --------------------

   function E_Compl_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Ada_To_Why.Cursor := Compl_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Symbol,
                 Name     => Full_Name (E) & "__compl");
         begin
            Compl_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Compl_Module;

   -------------------
   -- E_Init_Module --
   -------------------

   function E_Init_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Ada_To_Why.Cursor := Init_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Symbol,
                 Name     =>
                   Full_Name (E) & To_String (WNE_Init_Wrapper_Suffix));
         begin
            Init_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Init_Module;

   ------------------------
   -- E_Rec_Axiom_Module --
   ------------------------

   function E_Rec_Axiom_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Ada_To_Why.Cursor := Rec_Axiom_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            Name : constant String :=
              Full_Name (E) & "__rec_axioms";
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Symbol,
                 Name     => Name);
         begin
            Rec_Axiom_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Rec_Axiom_Module;

   ------------------
   -- E_Rep_Module --
   ------------------

   function E_Rep_Module (E : Entity_Id) return W_Module_Id is
      use Ada_To_Why;
      C : constant Ada_To_Why.Cursor := Rep_Modules.Find (E);
   begin
      if Has_Element (C) then
         return W_Module_Id (Element (C));
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => E,
                 File     => No_Symbol,
                 Name     => Full_Name (E) & "__rep");
         begin
            Rep_Modules.Insert (E, Why_Node_Id (M));
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end E_Rep_Module;

   ------------------------
   -- Get_Logic_Function --
   ------------------------

   function Get_Logic_Function (E : Entity_Id) return W_Identifier_Id is
      Name : constant Symbol := Get_Profile_Theory_Name (E);
   begin
      return M_Subprogram_Profiles (Name).Call_Id;
   end Get_Logic_Function;

   ------------------------------
   -- Get_Logic_Function_Guard --
   ------------------------------

   function Get_Logic_Function_Guard (E : Entity_Id) return W_Identifier_Id is
      Name : constant Symbol := Get_Profile_Theory_Name (E);
   begin
      return M_Subprogram_Profiles (Name).Pred_Id;
   end Get_Logic_Function_Guard;

   ---------------------
   -- Get_Module_Name --
   ---------------------

   function Get_Module_Name (M : W_Module_Id) return String is
   begin
      return Img (Module_Get_Name (+M));
   end Get_Module_Name;

   -----------------------------
   -- Get_Profile_Theory_Name --
   -----------------------------

   function Get_Profile_Theory_Name (E : Entity_Id) return Symbol is
      Name      : Unbounded_String :=
        To_Unbounded_String ("profile");
      Type_Name : Unbounded_String;
      Mode_Name : Unbounded_String;
      Param     : Entity_Id := First_Formal (E);
   begin
      while Present (Param) loop
         Mode_Name := To_Unbounded_String
           (case Formal_Kind (Ekind (Param)) is
               when E_In_Parameter     => "__In",
               when E_Out_Parameter    => "__Out",
               when E_In_Out_Parameter => "__InOut");
         Type_Name := To_Unbounded_String
           ("__" &
              Capitalize_First
              (Full_Name (Retysp (Etype (Param)))));

         Name := Name & Mode_Name & Type_Name;

         Next_Formal (Param);
      end loop;

      if Ekind (E) = E_Function or else Is_Function_Type (E) then
         Type_Name := (To_Unbounded_String
                       ("__Return__" &
                            Capitalize_First
                            (Full_Name (Retysp (Etype (E))))));
         Name := Name & Type_Name;
      end if;

      return NID (To_String (Name));
   end Get_Profile_Theory_Name;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin

      --  Initialize files first

      Int_File  := NID ("int");
      Real_File := NID ("real");
      Ref_File  := NID ("ref");

      Gnatprove_Standard_File := NID ("_gnatprove_standard");
      Ada_Model_File          := NID ("ada__model");

      --  Modules of the Why standard library

      Int_Module := New_Module (File => Int_File,  Name => "Int");
      RealInfix  := New_Module (File => Real_File, Name => "RealInfix");
      Ref_Module := New_Module (File => Ref_File,  Name => "Ref");

      --  Builtin Why types

      EW_Bool_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb => NID ("bool")),
                  Is_Mutable => False);
      EW_Int_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb => NID ("int")),
                  Is_Mutable => False);
      EW_Prop_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb => NID ("prop")),
                  Is_Mutable => False);
      EW_Real_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb => NID ("real")),
                  Is_Mutable => False);
      EW_Unit_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb => NID ("unit")),
                  Is_Mutable => False);

      --  built-in void ident

      Init_Main_Module;
      Init_Compat_Tags_Module;
      Init_Integer_Module;
      Init_Int_Power_Module;
      Init_Int_Div_Module;
      Init_Int_Abs_Module;
      Init_Int_Minmax_Module;
      Init_Int_Gcd_Module;
      Init_BV_Modules;
      Init_BV_Conv_Modules;
      Init_Floating_Module;
      Init_Floating_Conv_Module;
      Init_Boolean_Module;
      Init_Real_Module;
      Init_Real_From_Int_Module;
      Init_Real_Power_Module;
      Init_Real_Abs_Module;
      Init_Real_Minmax_Module;
      Init_Subprogram_Access_Module;
      Init_Labels;
      Init_Builtin_From_Image_Module;
      --  modules of "ada__model" file

      Static_Modular_lt8 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_lt8");
      Static_Modular_lt16 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_lt16");
      Static_Modular_lt32 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_lt32");
      Static_Modular_lt64 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_lt64");
      Static_Modular_lt128 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_lt128");
      Static_Modular_8 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_8");
      Static_Modular_16 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_16");
      Static_Modular_32 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_32");
      Static_Modular_64 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_64");
      Static_Modular_128 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Modular_128");
      Static_Discrete :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Discrete");
      Dynamic_Modular :=
        New_Module
          (File => Ada_Model_File,
           Name => "Dynamic_Modular");
      Dynamic_Discrete :=
        New_Module
          (File => Ada_Model_File,
           Name => "Dynamic_Discrete");
      Static_Fixed_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Fixed_Point");
      Dynamic_Fixed_Point :=
        New_Module
          (File => Ada_Model_File,
           Name => "Dynamic_Fixed_Point");
      Fixed_Point_Rep :=
        New_Module
          (File => Ada_Model_File,
           Name => "Fixed_Point_Rep");
      Fixed_Point_Mult_Div :=
        New_Module
          (File => Ada_Model_File,
           Name => "Fixed_Point_Mult_Div");
      Static_Float32 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Float32");
      Static_Float64 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Static_Float64");
      Dynamic_Float :=
        New_Module
          (File => Ada_Model_File,
           Name => "Dynamic_Floating_Point");
      Rep_Proj_Float32 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_Float32");
      Rep_Proj_Float64 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_Float64");
      Rep_Proj_Fixed :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_Fixed");
      Rep_Proj_Int :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_Int");
      Rep_Proj_Lt8 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_ltBV8");
      Rep_Proj_Lt16 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_ltBV16");
      Rep_Proj_Lt32 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_ltBV32");
      Rep_Proj_Lt64 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_ltBV64");
      Rep_Proj_Lt128 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_ltBV128");
      Rep_Proj_8 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_BV8");
      Rep_Proj_16 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_BV16");
      Rep_Proj_32 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_BV32");
      Rep_Proj_64 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_BV64");
      Rep_Proj_128 :=
        New_Module
          (File => Ada_Model_File,
           Name => "Rep_Proj_BV128");
      Access_To_Incomp_Ty :=
        New_Module
          (File => Ada_Model_File,
           Name => "Access_to_incomplete_type");
      Pledge :=
        New_Module
          (File => Ada_Model_File,
           Name => "Pledge");

      Constr_Arrays :=
        (1 => New_Module (File => Ada_Model_File,
                          Name => "Constr_Array"),
         2 => New_Module (File => Ada_Model_File,
                          Name => "Constr_Array_2"),
         3 => New_Module (File => Ada_Model_File,
                          Name => "Constr_Array_3"),
         4 => New_Module (File => Ada_Model_File,
                          Name => "Constr_Array_4"));
      Unconstr_Arrays :=
        (1 => New_Module (File => Ada_Model_File,
                          Name => "Unconstr_Array"),
         2 => New_Module (File => Ada_Model_File,
                          Name => "Unconstr_Array_2"),
         3 => New_Module (File => Ada_Model_File,
                          Name => "Unconstr_Array_3"),
         4 => New_Module (File => Ada_Model_File,
                          Name => "Unconstr_Array_4"));

      Array_Concat_Axioms :=
        New_Module
          (File => Gnatprove_Standard_File,
           Name => "Array__1__Concat");

      Array_Int_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Array_Int_Rep_Comparison_Axiom");

      Array_BV8_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Array_BV8_Rep_Comparison_Axiom");

      Array_BV16_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Array_BV16_Rep_Comparison_Axiom");

      Array_BV32_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Array_BV32_Rep_Comparison_Axiom");

      Array_BV64_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Array_BV64_Rep_Comparison_Axiom");

      Array_BV128_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Array_BV128_Rep_Comparison_Axiom");

      Standard_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Standard_Array_Logical_Op_Axioms");

      Subtype_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File,
           Name => "Subtype_Array_Logical_Op_Axioms");

      --  Builtin unary minus and void

      Int_Unary_Minus :=
        New_Identifier (Domain => EW_Term,
                        Symb   => NID ("-"),
                        Typ    => EW_Int_Type);
      Fixed_Unary_Minus :=
        New_Identifier (Domain => EW_Term,
                        Symb   => NID ("-"),
                        Typ    => M_Main.Fixed_Type);
      Real_Unary_Minus :=
        New_Identifier (Domain => EW_Term,
                        Symb   => NID ("-."),
                        Typ    => EW_Real_Type);

      Void := New_Identifier (Domain => EW_Term,
                              Symb   => NID ("()"),
                              Typ    => EW_Unit_Type);

      --  Builtin infix operations

      Why_Eq :=
        New_Identifier (Domain => EW_Term,
                        Symb   => NID ("="),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Why_Neq :=
        New_Identifier (Domain => EW_Term,
                        Symb   => NID ("<>"),
                        Typ    => EW_Bool_Type,
                        Infix  => True);

      Int_Infix_Add :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("+"),
                        Typ    => EW_Int_Type,
                        Infix  => True);
      Int_Infix_Subtr :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("-"),
                        Typ    => EW_Int_Type,
                        Infix  => True);
      Int_Infix_Mult :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("*"),
                        Typ    => EW_Int_Type,
                        Infix  => True);
      Int_Infix_Le :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("<="),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Int_Infix_Lt :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("<"),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Int_Infix_Ge :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID (">="),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Int_Infix_Gt :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID (">"),
                        Typ    => EW_Bool_Type,
                        Infix  => True);

      Fixed_Infix_Add :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("+"),
                        Typ    => M_Main.Fixed_Type,
                        Infix  => True);
      Fixed_Infix_Subtr :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("-"),
                        Typ    => M_Main.Fixed_Type,
                        Infix  => True);
      Fixed_Infix_Mult :=
        New_Identifier (Module => Int_Module,
                        Domain => EW_Term,
                        Symb   => NID ("*"),
                        Typ    => M_Main.Fixed_Type,
                        Infix  => True);

      Real_Infix_Add :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("+."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Subtr :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("-."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Mult :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("*."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Div :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("/."),
                        Typ    => EW_Real_Type,
                        Infix  => True);
      Real_Infix_Le :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("<=."),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Real_Infix_Lt :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("<."),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Real_Infix_Ge :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID (">=."),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Real_Infix_Gt :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID (">."),
                        Typ    => EW_Bool_Type,
                        Infix  => True);
      Real_Infix_Eq :=
        New_Identifier (Module => RealInfix,
                        Domain => EW_Term,
                        Symb   => NID ("=."),
                        Typ    => EW_Bool_Type,
                        Infix  => True);

      --  String image module

      String_Image_Module :=
        New_Module
          (Ada_Node => Empty,
           File     => No_Symbol,
           Name     => "Standard_String__Img");

      To_String_Id :=
        New_Identifier (Ada_Node => Standard_String,
                        Domain   => EW_Term,
                        Module   => String_Image_Module,
                        Symb     => NID ("to_string"));

      Of_String_Id :=
        New_Identifier (Ada_Node => Standard_String,
                        Domain   => EW_Term,
                        Module   => String_Image_Module,
                        Symb     => NID ("from_string"));

      --  Other identifiers

      Old_Tag := NID ("old");
      Def_Name :=
        New_Identifier
          (Symb   => NID ("def"),
           Domain => EW_Term);

      --  Modules of _gnatprove_standard file

      Array_Modules :=
        (1 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => "Array__1"),
         2 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => "Array__2"),
         3 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => "Array__3"),
         4 =>
           New_Module (File => Gnatprove_Standard_File,
                       Name => "Array__4"));
   end Initialize;

   -----------------------
   -- Init_Array_Module --
   -----------------------

   function Init_Array_Module (Module : W_Module_Id) return M_Array_Type
   is
      M_Array : M_Array_Type;
      Ty      : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb   => NID ("map"),
                                          Module => Module),
                  Is_Mutable => False);
      Comp_Ty : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb   => NID ("component_type"),
                                          Module => Module),
                  Is_Mutable => False);
   begin
      M_Array.Module := Module;

      M_Array.Ty := Ty;
      M_Array.Comp_Ty := Comp_Ty;
      M_Array.Get :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("get"),
                        Typ    => Comp_Ty);
      M_Array.Set :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("set"),
                        Typ    => Ty);
      M_Array.Bool_Eq :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Array.Slide :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("slide"),
                        Typ    => Ty);

      return M_Array;
   end Init_Array_Module;

   -------------------------
   -- Init_Array_1_Module --
   -------------------------

   function Init_Array_1_Module (Module : W_Module_Id) return M_Array_1_Type
   is
      M_Array_1 : M_Array_1_Type;
      Ty : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb   => NID ("map"),
                                          Module => Module),
                  Is_Mutable => False);
   begin
      M_Array_1.Module := Module;
      M_Array_1.Concat :=
        (False =>
           (False =>
                New_Identifier (Module => Module,
                                Domain => EW_Term,
                                Symb   => NID ("concat"),
                                Typ    => Ty),
            True  =>
                New_Identifier (Module => Module,
                                Domain => EW_Term,
                                Symb   => NID ("concat_singleton_right"),
                                Typ    => Ty)),
         True  =>
           (False =>
                New_Identifier (Module => Module,
                                Domain => EW_Term,
                                Symb   => NID ("concat_singleton_left"),
                                Typ    => Ty),
            True  =>
                New_Identifier (Module => Module,
                                Domain => EW_Term,
                                Symb   => NID ("concat_singletons"),
                                Typ    => Ty)));
      M_Array_1.Singleton :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("singleton"),
                        Typ    => Ty);

      return M_Array_1;
   end Init_Array_1_Module;

   ------------------------------
   -- Init_Array_1_Comp_Module --
   ------------------------------

   function Init_Array_1_Comp_Module (Module : W_Module_Id)
                                      return M_Array_1_Comp_Type
   is
      M_Array_1 : M_Array_1_Comp_Type;

   begin
      M_Array_1.Module := Module;
      M_Array_1.Compare :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("compare"),
                        Typ    => EW_Int_Type);

      return M_Array_1;
   end Init_Array_1_Comp_Module;

   function Init_Array_1_Bool_Op_Module (Module : W_Module_Id)
                                      return M_Array_1_Bool_Op_Type
   is
      M_Array_1 : M_Array_1_Bool_Op_Type;
      Ty : constant W_Type_Id :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       => New_Name (Symb   => NID ("map"),
                                          Module => Module),
                  Is_Mutable => False);

   begin
      M_Array_1.Module := Module;
      M_Array_1.Xorb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("xorb"),
                        Typ    => Ty);
      M_Array_1.Andb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("andb"),
                        Typ    => Ty);
      M_Array_1.Orb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("orb"),
                        Typ    => Ty);
      M_Array_1.Notb :=
        New_Identifier (Module => Module,
                        Domain => EW_Term,
                        Symb   => NID ("notb"),
                        Typ    => Ty);

      return M_Array_1;
   end Init_Array_1_Bool_Op_Module;

   -------------------------
   -- Init_Boolean_Module --
   -------------------------

   procedure Init_Boolean_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Boolean");
   begin
      M_Boolean.Module := M;
      M_Boolean.Bool_Eq :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Ne :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Le :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Lt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Ge :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Bool_Gt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Notb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("notb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Andb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("andb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Notb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("notb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Orb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("orb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Xorb :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("xorb"),
                        Typ    => EW_Bool_Type);
      M_Boolean.To_Int :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("to_int"),
                        Typ    => EW_Int_Type);
      M_Boolean.Of_Int :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("of_int"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Range_Check :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("range_check_"),
                        Typ    => EW_Int_Type);
      M_Boolean.Check_Not_First :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("check_not_first"),
                        Typ    => EW_Int_Type);
      M_Boolean.Check_Not_Last :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("check_not_last"),
                        Typ    => EW_Int_Type);
      M_Boolean.First :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("first"),
                        Typ    => EW_Int_Type);
      M_Boolean.Last :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("last"),
                        Typ    => EW_Int_Type);
      M_Boolean.Range_Pred :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Dynamic_Prop :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("dynamic_property"),
                        Typ    => EW_Bool_Type);
      M_Boolean.Image :=
        New_Identifier
          (Symb   => NID ("attr__ATTRIBUTE_IMAGE"),
           Module => M,
           Domain => EW_Term,
           Typ    => M_Main.String_Image_Type);
      M_Boolean.Value :=
        New_Identifier
          (Symb   => NID ("attr__ATTRIBUTE_VALUE"),
           Module => M,
           Domain => EW_Term,
           Typ    => EW_Bool_Type);
   end Init_Boolean_Module;

   ------------------------------------
   -- Init_Builtin_From_Image_Module --
   ------------------------------------

   procedure Init_Builtin_From_Image_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Builtin_from_image");
   begin
      M_Builtin_From_Image.Int_Value :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("int__attr__ATTRIBUTE_VALUE"),
                        Typ    => EW_Int_Type);

      M_Builtin_From_Image.Real_Value :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("real__attr__ATTRIBUTE_VALUE"),
                        Typ    => EW_Real_Type);
   end Init_Builtin_From_Image_Module;

   --------------------------
   -- Init_BV_Conv_Modules --
   --------------------------

   procedure Init_BV_Conv_Modules is
      M : W_Module_Id;
   begin
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_128_256");
      M_BV_Conv_128_256 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_256_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_128_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_256_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_64_128");
      M_BV_Conv_64_128 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_128_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_64_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_128_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_32_128");
      M_BV_Conv_32_128 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_128_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_32_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_128_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_16_128");
      M_BV_Conv_16_128 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_128_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_16_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_128_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_8_128");
      M_BV_Conv_8_128 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_128_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_128_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_32_64");
      M_BV_Conv_32_64 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_64_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_32_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_64_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_16_64");
      M_BV_Conv_16_64 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_64_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_16_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_64_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_8_64");
      M_BV_Conv_8_64 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_64_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_64_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_16_32");
      M_BV_Conv_16_32 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_32_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_16_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_32_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_8_32");
      M_BV_Conv_8_32 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_32_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_32_Type));

      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "BVConv_8_16");
      M_BV_Conv_8_16 :=
        M_BV_Conv_Type'(Module => M,
                        To_Big =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toBig"),
                                          Typ    => EW_BitVector_16_Type),
                        To_Small =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("toSmall"),
                                          Typ    => EW_BitVector_8_Type),
                        Range_Check =>
                          New_Identifier (Module => M,
                                          Domain => EW_Term,
                                          Symb   => NID ("range_check_"),
                                          Typ    => EW_BitVector_16_Type));

   end Init_BV_Conv_Modules;

   ---------------------
   -- Init_BV_Modules --
   ---------------------

   procedure Init_BV_Modules is
   begin
      M_BVs (BV8).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "BV8");
      M_BVs (BV16).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "BV16");
      M_BVs (BV32).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "BV32");
      M_BVs (BV64).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "BV64");
      M_BVs (BV128).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "BV128");
      M_BVs (BV256).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "BV256");

      for BV in BV_Kind loop
         M_BVs (BV).T :=
           New_Type (Type_Kind  => EW_Builtin,
                     Name       => New_Name (Symb   => NID ("t"),
                                             Module => M_BVs (BV).Module),
                     Is_Mutable => False);
         M_BVs (BV).Ult :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("ult"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Ule :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("ule"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Ugt :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("ugt"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Uge :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("uge"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).BV_Min :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bv_min"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BV_Max :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bv_max"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Bool_Eq :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bool_eq"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Ne :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bool_ne"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Le :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bool_le"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Lt :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bool_lt"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Ge :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bool_ge"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Gt :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bool_gt"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Bool_Type);
         M_BVs (BV).One :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("one"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Add :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("add"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Sub :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("sub"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Neg :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("neg"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Mult :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("mul"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Power :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("power"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Udiv :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("udiv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Urem :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("urem"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Urem :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("urem"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_And :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bw_and"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Or :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bw_or"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Xor :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bw_xor"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Not :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("bw_not"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).BV_Abs :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("abs"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsl :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("lsl_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsr :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("lsr_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Asr :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("asr_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Rotate_Left :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("rotate_left_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Rotate_Right :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("rotate_right_bv"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).Of_Int :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("of_int"),
                           Module => M_BVs (BV).Module,
                           Typ    => M_BVs (BV).T);
         M_BVs (BV).To_Int :=
           New_Identifier (Domain => EW_Term,
                           Symb   => NID ("t_int"),
                           Module => M_BVs (BV).Module,
                           Typ    => EW_Int_Type);
         M_BVs (BV).Two_Power_Size :=
           New_Identifier (Module => M_BVs (BV).Module,
                           Domain => EW_Term,
                           Symb   => NID ("_two_power_size"),
                           Typ    => EW_Int_Type);
         M_BVs (BV).Prog_Eq :=
           New_Identifier (Module => M_BVs (BV).Module,
                           Domain => EW_Term,
                           Symb   => NID ("eq"),
                           Typ    => EW_Bool_Type);
         M_BVs (BV).Prog_Neq :=
           New_Identifier (Module => M_BVs (BV).Module,
                           Domain => EW_Term,
                           Symb   => NID ("neq"),
                           Typ    => EW_Bool_Type);
      end loop;

      EW_BitVector_8_Type   := M_BVs (BV8).T;
      EW_BitVector_16_Type  := M_BVs (BV16).T;
      EW_BitVector_32_Type  := M_BVs (BV32).T;
      EW_BitVector_64_Type  := M_BVs (BV64).T;
      EW_BitVector_128_Type := M_BVs (BV128).T;
      EW_BitVector_256_Type := M_BVs (BV256).T;
   end Init_BV_Modules;

   -----------------------------
   -- Init_Compat_Tags_Module --
   -----------------------------

   procedure Init_Compat_Tags_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Compatible_Tags");
   begin
      M_Compat_Tags.Module := M;
      M_Compat_Tags.Compat_Tags_Id :=
        New_Identifier (Domain => EW_Pred,
                        Module => M,
                        Symb   => NID ("__compatible_tags"),
                        Typ    => EW_Bool_Type);
   end Init_Compat_Tags_Module;

   -------------------------------
   -- Init_Floating_Conv_Module --
   -------------------------------

   procedure Init_Floating_Conv_Module is
      M : W_Module_Id;
   begin
      M := New_Module (File => Gnatprove_Standard_File,
                       Name => "FloatConv");
      M_Floating_Conv :=
        M_Floating_Conv_Type'(Module      => M,
                              To_Float64  =>
                                New_Identifier (Module => M,
                                                Domain => EW_Term,
                                                Symb   =>
                                                  NID ("to_float64_rne"),
                                                Typ    => EW_Float_64_Type),
                              To_Float32  =>
                                New_Identifier (Module => M,
                                                Domain => EW_Term,
                                                Symb   =>
                                                  NID ("to_float32_rne"),
                                                Typ    => EW_Float_32_Type),
                              Range_Check =>
                                New_Identifier (Module => M,
                                                Domain => EW_Term,
                                                Symb   => NID ("range_check_"),
                                                Typ    => EW_Float_64_Type));
   end Init_Floating_Conv_Module;

   --------------------------
   -- Init_Floating_Module --
   --------------------------

   procedure Init_Floating_Module is
      Float32_BV_Converter : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float32_BV_Converter");
      Float64_BV_Converter : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float64_BV_Converter");
   begin
      M_Floats (Float32).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float32");
      M_Floats (Float64).Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float64");
      M_Floats (Float32).Power_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float32_power");
      M_Floats (Float64).Power_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float64_power");
      M_Floats (Float32).Next_Prev_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float32_next_prev");
      M_Floats (Float64).Next_Prev_Module :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Float64_next_prev");

      for Fl in Floating_Kind loop
         M_Floats (Fl).T :=
           New_Type (Type_Kind  => EW_Builtin,
                     Name       => New_Name (Symb   => NID ("t"),
                                             Module => M_Floats (Fl).Module),
                     Is_Mutable => False);
         M_Floats (Fl).Bool_Eq :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("bool_eq"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Ne :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("bool_neq"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Le :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("bool_le"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Lt :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("bool_lt"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Ge :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("bool_ge"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Gt :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("bool_gt"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Max :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("max"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Min :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("min"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Abs_Float :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("abs"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Ceil :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("ceil"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Floor :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("floor"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Is_Finite :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("t'isFinite"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Power :=
           New_Identifier (Module => M_Floats (Fl).Power_Module,
                           Domain => EW_Term,
                           Symb   => NID ("power"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).To_Int :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("to_int_rna"),
                           Typ    => EW_Int_Type);
         M_Floats (Fl).Rounding :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("rounding"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_Int :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("of_int_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Truncate :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("truncate"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Unary_Minus :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("neg"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Add :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("add_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Subtr :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("sub_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Mult :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("mul_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Div :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("div_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Remainder :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("rem"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Le :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("le"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Lt :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("lt"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Ge :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("ge"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Gt :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("gt"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Eq :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("eq"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Neq :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("neq"),
                           Typ    => EW_Bool_Type);
         M_Floats (Fl).Prev_Rep :=
           New_Identifier (Module => M_Floats (Fl).Next_Prev_Module,
                           Domain => EW_Term,
                           Symb   => NID ("prev_representable"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Next_Rep :=
           New_Identifier (Module => M_Floats (Fl).Next_Prev_Module,
                           Domain => EW_Term,
                           Symb   => NID ("next_representable"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Plus_Zero :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("_zeroF"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).One :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("one"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Sqrt :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("sqrt_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV8 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv8_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV16 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv16_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV32 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv32_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV64 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv64_rne"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV8_RTN :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv8_rtn"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV16_RTN :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv16_rtn"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV32_RTN :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv32_rtn"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV64_RTN :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv64_rtn"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV8_RTP :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv8_rtp"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV16_RTP :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv16_rtp"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV32_RTP :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv32_rtp"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_BV64_RTP :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("of_ubv64_rtp"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).To_BV8 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("to_ubv8_rna"),
                           Typ    => EW_BitVector_8_Type);
         M_Floats (Fl).To_BV16 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("to_ubv16_rna"),
                           Typ    => EW_BitVector_16_Type);
         M_Floats (Fl).To_BV32 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("to_ubv32_rna"),
                           Typ    => EW_BitVector_32_Type);
         M_Floats (Fl).To_BV64 :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("to_ubv64_rna"),
                           Typ    => EW_BitVector_64_Type);
         M_Floats (Fl).Range_Check :=
           New_Identifier (Module => (if Fl = Float32
                                      then Float32_BV_Converter
                                      else Float64_BV_Converter),
                           Domain => EW_Term,
                           Symb   => NID ("range_check_"),
                           Typ    => M_Floats (Fl).T);
         M_Floats (Fl).To_Real :=
           New_Identifier (Module => M_Floats (Fl).Module,
                           Domain => EW_Term,
                           Symb   => NID ("to_real"),
                           Typ    => EW_Int_Type);
      end loop;

      EW_Float_32_Type := M_Floats (Float32).T;
      EW_Float_64_Type := M_Floats (Float64).T;
   end Init_Floating_Module;

   -------------------------
   -- Init_Int_Abs_Module --
   -------------------------

   procedure Init_Int_Abs_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Int_Abs");
   begin
      M_Int_Abs.Module := M;
      M_Int_Abs.Abs_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("abs"),
                        Typ    => EW_Int_Type);
   end Init_Int_Abs_Module;

   -------------------------
   -- Init_Int_Div_Module --
   -------------------------

   procedure Init_Int_Div_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Int_Division");
   begin
      M_Int_Div.Module := M;
      M_Int_Div.Div :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("div"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Euclid :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("euclid_div"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Rem_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("rem"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Mod_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("mod"),
                        Typ    => EW_Int_Type);
      M_Int_Div.Math_Mod :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("math_mod"),
                        Typ    => EW_Int_Type);
   end Init_Int_Div_Module;

   ---------------------------
   -- Init_Int_Gcd_Module --
   ---------------------------

   procedure Init_Int_Gcd_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Int_Gcd");
   begin
      M_Int_Gcd.Module := M;
      M_Int_Gcd.Gcd :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("gcd"),
                        Typ    => EW_Int_Type);
   end Init_Int_Gcd_Module;

   ----------------------------
   -- Init_Int_Minmax_Module --
   ----------------------------

   procedure Init_Int_Minmax_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Int_Minmax");

   begin
      M_Int_Minmax.Module := M;
      M_Int_Minmax.Max :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("int_max"),
                        Typ    => EW_Int_Type);
      M_Int_Minmax.Min :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("int_min"),
                        Typ    => EW_Int_Type);
   end Init_Int_Minmax_Module;

   ---------------------------
   -- Init_Int_Power_Module --
   ---------------------------

   procedure Init_Int_Power_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Int_Power");
   begin
      M_Int_Power.Module := M;
      M_Int_Power.Power :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("power"),
                        Typ    => EW_Int_Type);
   end Init_Int_Power_Module;

   -------------------------
   -- Init_Integer_Module --
   -------------------------

   procedure Init_Integer_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Integer");
   begin
      M_Integer.Module := M;
      M_Integer.Bool_Eq :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Ne :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Le :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Lt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Ge :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      M_Integer.Bool_Gt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);
      M_Integer.Length :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("length"),
                        Typ    => EW_Int_Type);
   end Init_Integer_Module;

   -----------------
   -- Init_Labels --
   -----------------

   procedure Init_Labels is
   begin
      Model_Trace       := NID (Model_Trace_Label);
      Model_Projected   := NID (Model_Proj_Label);
      VC_Annotation     := NID (VC_Annotation_Label);
      Model_VC_Post     := NID (Model_VC_Post_Label);
      GP_Already_Proved := NID (GP_Already_Proved_Marker);
   end Init_Labels;

   ----------------------
   -- Init_Main_Module --
   ----------------------

   procedure Init_Main_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Main");
   begin
      M_Main.Module := M;
      M_Main.String_Image_Type :=
        New_Type (Type_Kind  => EW_Abstract,
                  Name       =>
                    New_Name (Symb => NID ("__image"), Module => M),
                  Is_Mutable => False);

      M_Main.Type_Of_Heap :=
        New_Type (Type_Kind  => EW_Abstract,
                  Name       => New_Name (Symb   => NID ("__type_of_heap"),
                                          Module => M),
                  Is_Mutable => False);
      M_Main.Fixed_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       =>
                    New_Name (Symb => NID ("__fixed"), Module => M),
                  Is_Mutable => False);
      M_Main.Private_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       =>
                    New_Name (Symb => NID ("__private"), Module => M),
                  Is_Mutable => False);
      M_Main.Private_Bool_Eq :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("private__bool_eq"),
                        Typ    => EW_Bool_Type);

      M_Main.Return_Exc :=
        New_Name (Symb => NID ("Return__exc"));

      M_Main.Null_Extension :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("__null_ext__"),
                        Typ    => M_Main.Private_Type);

      M_Main.Spark_CE_Branch :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("spark__branch"),
                        Typ    => EW_Bool_Type);

      EW_Private_Type := M_Main.Private_Type;

      M_Main.No_Return :=
        New_Identifier (Domain => EW_Term,
                        Module => M,
                        Symb   => NID ("no__return"),
                        Typ    => EW_Bool_Type);
   end Init_Main_Module;

   --------------------------
   -- Init_Real_Abs_Module --
   --------------------------

   procedure Init_Real_Abs_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Real_Abs");
   begin
      M_Real_Abs.Module := M;
      M_Real_Abs.Abs_Id :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("abs"),
                        Typ    => EW_Real_Type);
   end Init_Real_Abs_Module;

   -------------------------------
   -- Init_Real_From_Int_Module --
   -------------------------------

   procedure Init_Real_From_Int_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Real_FromInt");

   begin
      M_Real_From_Int.Module := M;
      M_Real_From_Int.From_Int :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("from_int"),
                        Typ    => EW_Real_Type);
   end Init_Real_From_Int_Module;

   -----------------------------
   -- Init_Real_Minmax_Module --
   -----------------------------

   procedure Init_Real_Minmax_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Real_Minmax");

   begin
      M_Real_Minmax.Module := M;
      M_Real_Minmax.Max :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("max"),
                        Typ    => EW_Real_Type);
      M_Real_Minmax.Min :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("min"),
                        Typ    => EW_Real_Type);
   end Init_Real_Minmax_Module;

   ----------------------
   -- Init_Real_Module --
   ----------------------

   procedure Init_Real_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Real");
   begin
      M_Real.Module := M;
      M_Real.Bool_Eq :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_eq"),
                        Typ    => EW_Bool_Type);
      M_Real.Bool_Ne :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_ne"),
                        Typ    => EW_Bool_Type);
      M_Real.Bool_Le :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_le"),
                        Typ    => EW_Bool_Type);
      M_Real.Bool_Lt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_lt"),
                        Typ    => EW_Bool_Type);
      M_Real.Bool_Ge :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_ge"),
                        Typ    => EW_Bool_Type);
      M_Real.Bool_Gt :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("bool_gt"),
                        Typ    => EW_Bool_Type);
   end Init_Real_Module;

   ----------------------------
   -- Init_Real_Power_Module --
   ----------------------------

   procedure Init_Real_Power_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Real_Power");
   begin
      M_Real_Power.Module := M;
      M_Real_Power.Power :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("power"),
                        Typ    => EW_Real_Type);
   end Init_Real_Power_Module;

   -----------------------------------
   -- Init_Subprogram_Access_Module --
   -----------------------------------

   procedure Init_Subprogram_Access_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File,
                    Name => "Subprogram_Pointer_Rep");
   begin
      M_Subprogram_Access.Module := M;
      M_Subprogram_Access.Subprogram_Type :=
        New_Type (Type_Kind  => EW_Builtin,
                  Name       =>
                    New_Name (Symb => NID ("__subprogram"), Module => M),
                  Is_Mutable => False);
      M_Subprogram_Access.Access_Rep_Type :=
        New_Name (Symb => NID ("__rep"), Module => M);
      M_Subprogram_Access.Rec_Is_Null :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("__is_null_pointer"),
                        Typ    => EW_Bool_Type);
      M_Subprogram_Access.Rec_Value :=
        New_Identifier (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("__pointer_value"),
                        Typ    => M_Subprogram_Access.Subprogram_Type);
      M_Subprogram_Access.Rec_Value_Prog :=
        New_Identifier (Module => M,
                        Domain => EW_Prog,
                        Symb   => NID ("__pointer_value_"),
                        Typ    => M_Subprogram_Access.Subprogram_Type);
   end Init_Subprogram_Access_Module;

   -------------------------
   -- Insert_Extra_Module --
   -------------------------

   procedure Insert_Extra_Module
     (N        : Node_Id;
      M        : W_Module_Id;
      Is_Axiom : Boolean := False) is
   begin
      if Is_Axiom then
         Axiom_Modules.Insert (N, Why_Node_Id (M));
      else
         Entity_Modules.Insert (N, Why_Node_Id (M));
      end if;
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
      --  Add the symbols for type entity E
      --  @param E a type entity

      procedure Insert_Object_Symbols (E : Entity_Id)
        with Pre => Is_Object (E);
      --  Add the symbols for object entity E
      --  @param E an object entity

      procedure Insert_Subprogram_Symbols (E : Entity_Id)
        with Pre => Is_Subprogram_Or_Entry (E);
      --  Add the symbols for subprogram or entry entity E
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
         Rec  : constant Entity_Id :=
           (if Ekind (E) in E_Component | E_Discriminant
            then Enclosing_Type (E)
            else E);
         M    : constant W_Module_Id := E_Module (Rec);
         Name : constant String :=
           (if Ekind (E) in E_Component | E_Discriminant
            then Full_Name (Representative_Component (E))
            else Short_Name (E));

      begin
         Insert_Symbol
           (E, WNE_Attr_Address,
            New_Identifier
              (Symb   => NID ("attr__ATTRIBUTE_ADDRESS"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));
         Insert_Symbol
           (E, WNE_Attr_First_Bit,
            New_Identifier
              (Symb   => NID (Name & "__first__bit"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));
         Insert_Symbol
           (E, WNE_Attr_Last_Bit,
            New_Identifier
              (Symb   => NID (Name & "__last__bit"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));
         Insert_Symbol
           (E, WNE_Attr_Position,
            New_Identifier
              (Symb   => NID (Name & "__position"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));

      end Insert_Object_Symbols;

      -------------------------------
      -- Insert_Subprogram_Symbols --
      -------------------------------

      procedure Insert_Subprogram_Symbols (E : Entity_Id) is
         M    : constant W_Module_Id := E_Module (E);
         M_Ax : constant W_Module_Id := E_Axiom_Module (E);
         Name : constant String := Short_Name (E);

      begin
         Insert_Symbol
           (E, WNE_Check_Invariants_On_Call,
            New_Identifier
              (Symb   => NID (Name & "__check_invariants_on_call"),
               Module => M_Ax,
               Domain => EW_Prog,
               Typ    => EW_Unit_Type));

         if Ekind (E) = E_Function then
            Insert_Symbol
              (E, WNE_Func_Guard,
               New_Identifier
                 (Symb   => NID (Name & "__" & Function_Guard),
                  Module => M,
                  Domain => EW_Pred,
                  Typ    => EW_Unit_Type));

            if Entity_Body_In_SPARK (E)
              and then Has_Contracts (E, Pragma_Refined_Post)
            then
               Insert_Symbol
                 (E, WNE_Refined_Func_Guard,
                  New_Identifier
                    (Symb      => NID (Name & "__" & Function_Guard),
                     Module    => M,
                     Namespace => NID (To_String (WNE_Refine_Module)),
                     Domain    => EW_Pred,
                     Typ       => EW_Unit_Type));
            end if;

            if Is_Visible_Dispatching_Operation (E) then
               Insert_Symbol
                 (E, WNE_Dispatch_Func_Guard,
                  New_Identifier
                    (Symb      => NID (Name & "__" & Function_Guard),
                     Module    => M,
                     Namespace => NID (To_String (WNE_Dispatch_Module)),
                     Domain    => EW_Pred,
                     Typ       => EW_Unit_Type));
            end if;
         elsif Is_Visible_Dispatching_Operation (E) then
            Insert_Symbol
              (E, WNE_Specific_Post,
               New_Identifier
                 (Symb      => NID (Name & "__" & Specific_Post),
                  Module    => M,
                  Namespace => NID (To_String (WNE_Dispatch_Module)),
                  Domain    => EW_Pred,
                  Typ       => EW_Unit_Type));
         end if;

         if Present (Get_Pragma (E, Pragma_Subprogram_Variant)) then
            Insert_Symbol
              (E, WNE_Check_Subprogram_Variants,
               New_Identifier
                 (Symb   => NID (Name & "__check_subprogram_variants"),
                  Module => M_Ax,
                  Domain => EW_Prog,
                  Typ    => EW_Unit_Type));
         end if;
      end Insert_Subprogram_Symbols;

      -------------------------
      -- Insert_Type_Symbols --
      -------------------------

      procedure Insert_Type_Symbols (E : Entity_Id) is
         M    : constant W_Module_Id := E_Module (E);
         AM   : constant W_Module_Id := E_Axiom_Module (E);
         Name : constant String := Short_Name (E);
         Ty   : constant W_Type_Id   := EW_Abstract (E);

      begin
         --  Insert symbols for the initialization wrapper if any. We need
         --  extra fields to create the wrapper type for scalars and simple
         --  private types, and conversion functions to and from the wrapper
         --  types for scalars, private types, and records. For array,
         --  conversion goes through the base array type, so conversion
         --  functions are rather stored with other array conversion theories.

         if Might_Contain_Relaxed_Init (E)
           and then (Is_Scalar_Type (E) or else Is_Record_Type_In_Why (E))
         then
            declare
               WM  : constant W_Module_Id := E_Init_Module (E);
            begin
               if Has_Scalar_Type (E)
                 or else Is_Simple_Private_Type (E)
               then
                  Insert_Symbol
                    (E, WNE_Init_Value,
                     New_Identifier
                       (Symb   => NID ("rec__value"),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => Ty));
                  Insert_Symbol
                    (E, WNE_Attr_Init,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Attr_Init)),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));
               end if;
               Insert_Symbol
                 (E, WNE_To_Wrapper,
                  New_Identifier
                    (Symb   => NID ("to_wrapper"),
                     Module => WM,
                     Domain => EW_Term,
                     Typ    => Ty));
               Insert_Symbol
                 (E, WNE_Of_Wrapper,
                  New_Identifier
                    (Symb   => NID ("of_wrapper"),
                     Module => WM,
                     Domain => EW_Term,
                     Typ    => EW_Init_Wrapper (Ty)));
            end;
         end if;

         Insert_Symbol
           (E, WNE_Bool_Eq,
            New_Identifier
              (Symb   => NID ("bool_eq"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Bool_Type));

         Insert_Symbol
           (E, WNE_Dummy,
            New_Identifier
              (Symb   => NID ("dummy"),
               Module => M,
               Domain => EW_Term,
               Typ    => Ty));

         --  Add symbol for the function checking that the predicate of a type
         --  holds. This symbol is registered in the axiom module, so that
         --  the function can be directly defined there instead of being first
         --  declared in the entity module and then axiomatized in the axiom
         --  module (to have visibility over constants/functions in the
         --  definition).

         if Has_Predicates (E) then
            Insert_Symbol
              (E, WNE_Dynamic_Predicate,
               New_Identifier
                 (Symb   => NID ("dynamic_predicate"),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
         end if;

         --  Add symbol for the predicate used to assume the dynamic invariant
         --  of a type. This symbol is registered in the axiom module, so that
         --  the function can be directly defined there instead of being first
         --  declared in the entity module and then axiomatized in the axiom
         --  module (to have visibility over constants/functions in the
         --  definition).

         if not Is_Itype (E) then
            Insert_Symbol
              (E, WNE_Dynamic_Invariant,
               New_Identifier
                 (Symb   => NID ("dynamic_invariant"),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
         end if;

         --  Add symbol for the function checking that the invariant of a type
         --  holds. This symbol is registered in the axiom module, so that
         --  the function can be directly defined there instead of being first
         --  declared in the entity module and then axiomatized in the axiom
         --  module (to have visibility over constants/functions in the
         --  definition).

         if Has_Invariants_In_SPARK (E) then
            Insert_Symbol
              (E, WNE_Type_Invariant,
               New_Identifier
                 (Symb   => NID ("type_invariant"),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
         end if;

         --  Add symbol for the predicate used to assume the initial value of
         --  default initialized variables of a type. This symbol is registered
         --  in the axiom module, so that the function can be directly defined
         --  there instead of being first declared in the entity module and
         --  then axiomatized in the axiom module (to have visibility over
         --  constants/functions in the definition).

         if not Is_Itype (E) and then Can_Be_Default_Initialized (E) then
            Insert_Symbol
              (E, WNE_Default_Init,
               New_Identifier
                 (Symb   => NID ("default_initial_assumption"),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
         end if;

         if Is_Deep (E)
           and then not Has_Access_Type (E)
         then
            Insert_Symbol
              (E, WNE_Is_Moved,
               New_Identifier
                 (Symb   => NID (To_String (WNE_Is_Moved)),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
            Insert_Symbol
              (E, WNE_Move,
               New_Identifier
                 (Symb   => NID (To_String (WNE_Move)),
                  Module => AM,
                  Domain => EW_Prog));
            Insert_Symbol
              (E, WNE_Moved_Relation,
               New_Identifier
                 (Symb   => NID (To_String (WNE_Moved_Relation)),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
         end if;

         --  Symbols for scalar types

         if Is_Scalar_Type (E) then
            declare
               Base : constant W_Type_Id :=
                 Get_EW_Term_Type (E);
            begin
               Insert_Symbol
                 (E, WNE_Attr_Image,
                  New_Identifier
                    (Symb   => NID ("attr__ATTRIBUTE_IMAGE"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => M_Main.String_Image_Type));
               Insert_Symbol
                 (E, WNE_Attr_Value,
                  New_Identifier
                    (Symb   => NID ("attr__ATTRIBUTE_VALUE"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Check_Not_First,
                  New_Identifier
                    (Symb   => NID ("check_not_first"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Check_Not_Last,
                  New_Identifier
                    (Symb   => NID ("check_not_last"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Range_Check_Fun,
                  New_Identifier
                    (Symb   => NID ("range_check_"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Dynamic_Property,
                  New_Identifier
                    (Symb   => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));

               --  For types translated to range types in Why, declare
               --  predifined projection function.

               if Is_Range_Type_In_Why (E) then
                  Insert_Symbol
                    (E, WNE_Int_Proj,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID (Name & "'int"),
                        Typ    => EW_Int_Type));
               end if;

               declare
                  RM : constant W_Module_Id :=
                    (if Is_Scalar_Type (E)
                     and then not Type_Is_Modeled_As_Base (E)
                     then E_Rep_Module (E)
                     else M);

               begin
                  Insert_Symbol
                    (E, WNE_To_Rep,
                     New_Identifier
                       (Module => RM,
                        Domain => EW_Term,
                        Symb   => NID ("to_rep"),
                        Typ    => Base));

                  Insert_Symbol
                    (E, WNE_Of_Rep,
                     New_Identifier
                       (Module => RM,
                        Domain => EW_Term,
                        Symb   => NID ("of_rep"),
                        Typ    => Ty));
               end;

               Insert_Symbol
                 (E, WNE_Attr_First,
                  New_Identifier
                    (Symb   => NID ("first"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E, WNE_Attr_Last,
                  New_Identifier
                    (Symb   => NID ("last"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));

               --  Symbols for static scalar types

               if not Type_Is_Modeled_As_Base (E) then
                  Insert_Symbol
                    (E, WNE_Range_Pred,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type));
               end if;

               --  Symbols for modular types

               if Has_Modular_Integer_Type (E) then
                  declare
                     RM : constant W_Module_Id := E_Rep_Module (E);

                     To_Int : constant W_Identifier_Id :=
                       New_Identifier
                         (Symb   => NID ("to_int"),
                          Module => RM,
                          Domain => EW_Term,
                          Typ    => EW_Int_Type);
                  begin
                     Insert_Symbol (E, WNE_To_Int, To_Int);
                     Insert_Symbol (E, WNE_To_BitVector, To_Int);
                     Insert_Symbol
                       (E, WNE_Of_BitVector,
                        New_Identifier
                          (Symb   => NID ("of_int"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => Base));
                     Insert_Symbol
                       (E, WNE_Dynamic_Property_BV_Int,
                        New_Identifier
                          (Symb   => NID ("dynamic_property_int"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                     Insert_Symbol
                       (E, WNE_Attr_Modulus,
                        New_Identifier
                          (Symb   => NID ("attr__ATTRIBUTE_MODULUS"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => Base));
                     Insert_Symbol
                       (E, WNE_Range_Check_Fun_BV_Int,
                        New_Identifier
                          (Symb   => NID ("range_check_int_"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                  end;
               end if;

               --  Symbols for modular static types

               if Has_Modular_Integer_Type (E)
                 and then not Type_Is_Modeled_As_Base (E)
               then
                  Insert_Symbol
                    (E, WNE_Range_Pred_BV_Int,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range_int"),
                        Typ    => EW_Bool_Type));
               end if;

               --  Symbols for fixed point types

               if Is_Fixed_Point_Type (E) then
                  Insert_Symbol
                    (E, WNE_Small_Num,
                     New_Identifier
                       (Symb   => NID ("num_small"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));
                  Insert_Symbol
                    (E, WNE_Small_Den,
                     New_Identifier
                       (Symb   => NID ("den_small"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));

               --  Symbol for enum_rep attribute of enumeration types

               elsif Is_Enumeration_Type (E)
                 and then Has_Enumeration_Rep_Clause (E)
               then
                  Insert_Symbol
                    (E, WNE_Pos_To_Rep,
                     New_Identifier
                       (Symb   => NID ("pos_to_rep"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
               end if;
            end;

         --  Symbols for record types

         elsif Is_Record_Type_In_Why (E) then
            declare
               Root    : constant Entity_Id :=
                 Root_Retysp (E);
               Root_Ty : constant W_Type_Id :=
                 New_Named_Type (To_Why_Type (Root));
            begin
               Insert_Symbol
                 (E, WNE_Attr_Alignment,
                  New_Identifier
                    (Symb   => NID ("alignment"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Value_Size,
                  New_Identifier
                    (Symb   => NID ("value__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Object_Size,
                  New_Identifier
                    (Symb   => NID ("object__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));

               if Root = E
                 and then Has_Discriminants (E)
                 and then not Is_Constrained (E)
               then
                  Insert_Symbol
                    (E, WNE_Range_Check_Fun,
                     New_Identifier
                       (Symb   => NID ("range_check_"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Root_Ty));
                  Insert_Symbol
                    (E, WNE_Range_Pred,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type));
               end if;

               Insert_Symbol
                 (E, WNE_To_Base,
                  New_Identifier
                    (Symb   => NID ("to_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Root_Ty));
               Insert_Symbol
                 (E, WNE_Of_Base,
                  New_Identifier
                    (Symb   => NID ("of_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty));
               Insert_Symbol
                 (E, WNE_Rec_Split_Discrs,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Split_Discrs)),
                     Module => M,
                     Domain => EW_Term));
               Insert_Symbol
                 (E, WNE_Rec_Split_Fields,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Split_Fields)),
                     Module => M,
                     Domain => EW_Term));

               --  For types which have their own private part, introduce a
               --  symbol for the type of the component modelling this part
               --  and equality on it.

               if Has_Private_Part (E)
                 and then not Is_Simple_Private_Type (E)
               then
                  declare
                     WM        : constant W_Module_Id := E_Init_Module (E);
                     Main_Type : constant W_Identifier_Id :=
                       New_Identifier
                         (Symb   => NID ("__main_type"),
                          Module => M,
                          Domain => EW_Term);
                  begin
                     Insert_Symbol
                       (E, WNE_Private_Type, Main_Type);
                     Insert_Symbol
                       (E, WNE_Private_Eq,
                        New_Identifier
                          (Symb   => NID ("__main_eq"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));

                     --  If the type needs a wrapper for relaxed
                     --  initialization, introduce names for the components of
                     --  this wrapper and for conversion functions.

                     if Might_Contain_Relaxed_Init (E) then
                        Insert_Symbol
                          (E, WNE_Init_Value,
                           New_Identifier
                             (Symb   => NID ("rec__value"),
                              Module => WM,
                              Domain => EW_Term,
                              Typ    => New_Named_Type
                                (Name => Get_Name (Main_Type))));
                        Insert_Symbol
                          (E, WNE_Attr_Init,
                           New_Identifier
                             (Symb   => NID (To_String (WNE_Attr_Init)),
                              Module => WM,
                              Domain => EW_Term,
                              Typ    => EW_Bool_Type));
                        Insert_Symbol
                          (E, WNE_Private_To_Wrapper,
                           New_Identifier
                             (Symb   => NID ("__main_to_wrapper"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    => New_Named_Type
                                (Name         =>
                                     Get_Name (To_Init_Module (Main_Type)),
                                 Relaxed_Init => True)));
                        Insert_Symbol
                          (E, WNE_Private_Of_Wrapper,
                           New_Identifier
                             (Symb   => NID ("__main_of_wrapper"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    => New_Named_Type
                                (Name => Get_Name (Main_Type))));
                     end if;
                  end;
               end if;

               if Is_Tagged_Type (E) then
                  Insert_Symbol
                    (E, WNE_Dispatch_Eq,
                     New_Identifier
                       (Symb   => NID ("__dispatch_eq"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));
                  Insert_Symbol
                    (E, WNE_Attr_Tag,
                     New_Identifier
                       (Symb   => NID ("attr__tag"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E, WNE_Tag,
                     New_Identifier
                       (Symb   => NID ("__tag"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E, WNE_Rec_Extension,
                     New_Identifier
                       (Symb   => NID ("rec__ext__"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Private_Type));
               end if;

               if Has_Defaulted_Discriminants (E) then
                  Insert_Symbol
                    (E, WNE_Attr_Constrained,
                     New_Identifier
                       (Symb   => NID ("attr__constrained"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));
               end if;
            end;

         --  Symbols for array types

         elsif Has_Array_Type (E) then
            declare
               Ar_Dim : constant Positive := Positive (Number_Dimensions (E));
            begin
               Insert_Symbol
                 (E, WNE_Attr_Alignment,
                  New_Identifier
                    (Symb   => NID ("alignment"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Value_Size,
                  New_Identifier
                    (Symb   => NID ("value__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Object_Size,
                  New_Identifier
                    (Symb   => NID ("object__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Attr_Component_Size,
                  New_Identifier
                    (Symb   => NID ("component__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E, WNE_Dynamic_Property,
                  New_Identifier
                    (Symb   => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));
               Insert_Symbol
                 (E, WNE_To_Array,
                  New_Identifier
                    (Symb   => NID ("to_array"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Get_Array_Theory (E).Ty));
               Insert_Symbol
                 (E, WNE_Of_Array,
                  New_Identifier
                    (Symb   => NID ("of_array"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty));
               Insert_Symbol
                 (E, WNE_Array_Elts,
                  New_Identifier
                    (Symb   => NID ("elts"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Get_Array_Theory (E).Ty));
               if Ar_Dim = 1 and then
                 Is_Discrete_Type (Component_Type (E))
               then
                  declare
                     RM : constant W_Module_Id :=
                       (if not Type_Is_Modeled_As_Base (E)
                        then E_Rep_Module (E)
                        else M);
                  begin
                     Insert_Symbol
                       (E, WNE_To_Rep,
                        New_Identifier
                          (Module => RM,
                           Domain => EW_Term,
                           Symb   => NID ("to_rep"),
                           Typ    => EW_Abstract (Component_Type (E))));
                  end;
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
                          (Symb   => NID (First_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_Attr_Last (Dim),
                        New_Identifier
                          (Symb   => NID (Last_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_Attr_Length (Dim),
                        New_Identifier
                          (Symb   => NID (Length_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_To_Int (Dim),
                        New_Identifier
                          (Symb   => NID (Int_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E, WNE_Array_Base_Range_Pred (Dim),
                        New_Identifier
                          (Symb   => NID (Base_Range_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                     Insert_Symbol
                       (E, WNE_Index_Dynamic_Property (Dim),
                        New_Identifier
                          (Symb   => NID (Index_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                  end;
               end loop;
            end;

         --  Symbols for access-to-subprogram types

         elsif Is_Access_Subprogram_Type (Retysp (E)) then
            Insert_Symbol
              (E, WNE_Null_Pointer,
               New_Identifier
                 (Symb   => NID ("__null_pointer"),
                  Module => M,
                  Domain => EW_Term,
                  Typ    => Ty));
            Insert_Symbol
              (E, WNE_Range_Pred,
               New_Identifier
                 (Module => M,
                  Domain => EW_Pred,
                  Symb   => NID ("__in_range"),
                  Typ    => EW_Bool_Type));
            Insert_Symbol
              (E, WNE_Pointer_Call,
               New_Identifier
                 (Module => AM,
                  Domain => EW_Prog,
                  Symb   => NID ("__call_"),
                  Typ    =>
                    (if Is_Function_Type
                         (Directly_Designated_Type (Retysp (E)))
                     then Type_Of_Node
                       (Etype (Directly_Designated_Type (Retysp (E))))
                     else EW_Unit_Type)));
            Insert_Symbol
              (E, WNE_Assign_Null_Check,
               New_Identifier
                 (Symb   => NID ("assign_null_check"),
                  Module => M,
                  Domain => EW_Term,
                  Typ    => Ty));

         --  Symbols for other access types

         elsif Has_Access_Type (E) then
            declare
               Is_Incompl     : constant Boolean :=
                 Designates_Incomplete_Type (Repr_Pointer_Type (E));
               Root           : constant Entity_Id := Root_Pointer_Type (E);
               Root_Ty        : constant W_Type_Id := EW_Abstract (Root);
               Full_Name_Node : constant String := Full_Name (Root);
               M_C            : constant W_Module_Id :=
                 (if Is_Incompl then E_Compl_Module (Repr_Pointer_Type (E))
                  else M);
               Des_Ty         : constant W_Type_Id :=
                 EW_Abstract (Directly_Designated_Type (Retysp (E)));

            begin
               Insert_Symbol
                 (E, WNE_Null_Pointer,
                  New_Identifier
                    (Symb   => NID ("__null_pointer"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Root_Ty));

               Insert_Symbol
                 (E, WNE_Is_Null_Pointer,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Comp_Prefix) &
                             Full_Name_Node & "__is_null_pointer"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));

               Insert_Symbol
                 (E, WNE_Is_Moved_Pointer,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Comp_Prefix) &
                       Full_Name_Node & To_String (WNE_Is_Moved_Pointer)),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));

               Insert_Symbol
                 (E, WNE_Pointer_Address,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Comp_Prefix) &
                       Full_Name_Node & "__pointer_address"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));

               Insert_Symbol
                 (E, WNE_Pointer_Value,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Comp_Prefix) &
                       Full_Name_Node & "__pointer_value"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Des_Ty));

               Insert_Symbol
                 (E, WNE_To_Base,
                  New_Identifier
                    (Symb   => NID ("to_base"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Root_Ty));
               Insert_Symbol
                 (E, WNE_Of_Base,
                  New_Identifier
                    (Symb   => NID ("of_base"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Ty));

               if Root /= Repr_Pointer_Type (E) then
                  Insert_Symbol
                    (E, WNE_Range_Check_Fun,
                     New_Identifier
                       (Symb   => NID ("range_check_"),
                        Module => M_C,
                        Domain => EW_Term,
                        Typ    => Root_Ty));
                  Insert_Symbol
                    (E, WNE_Range_Pred,
                     New_Identifier
                       (Module => M_C,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type));
               end if;

               Insert_Symbol
                 (E, WNE_Init_Allocator,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Init_Allocator)),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Ty));

               Insert_Symbol
                 (E, WNE_Uninit_Allocator,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Uninit_Allocator)),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Ty));

               Insert_Symbol
                 (E, WNE_Assign_Null_Check,
                  New_Identifier
                    (Symb   => NID ("assign_null_check"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Ty));

               if Is_Incompl then
                  Insert_Symbol
                    (E, WNE_Private_Type,
                     New_Identifier
                       (Symb   => NID ("__main_type"),
                        Module => M,
                        Domain => EW_Term));
                  Insert_Symbol
                    (E, WNE_Pointer_Value_Abstr,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Rec_Comp_Prefix) &
                          Full_Name_Node & "__pointer_value_abstr"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => New_Named_Type
                          (Name => New_Name
                               (Symb   => NID ("__main_type"),
                                Module => M))));
                  Insert_Symbol
                    (E, WNE_Pointer_Open,
                     New_Identifier
                       (Symb   => NID ("__open"),
                        Module => M_C,
                        Domain => EW_Term,
                        Typ    => Des_Ty));
                  Insert_Symbol
                    (E, WNE_Pointer_Close,
                     New_Identifier
                       (Symb   => NID ("__close"),
                        Module => M_C,
                        Domain => EW_Term,
                        Typ    => New_Named_Type
                          (Name => New_Name
                               (Symb   => NID ("__main_type"),
                                Module => M))));
               end if;
            end;
         end if;
      end Insert_Type_Symbols;

   --  Start of processing for Insert_Why_Symbols

   begin
      if Is_Type (E) then
         Insert_Type_Symbols (E);
      elsif Is_Object (E) then
         Insert_Object_Symbols (E);
      elsif Is_Subprogram_Or_Entry (E) then
         Insert_Subprogram_Symbols (E);
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
      elsif T = EW_BitVector_128_Type then
         return M_BVs (BV128);
      elsif T = EW_BitVector_256_Type then
         return M_BVs (BV256);
      else
         raise Program_Error;
      end if;
   end MF_BVs;

   ---------------
   -- MF_Floats --
   ---------------

   function MF_Floats (T : W_Type_Id) return M_Floating_Type is
   begin
      if T = EW_Float_32_Type then
         return M_Floats (Float32);
      elsif T = EW_Float_64_Type then
         return M_Floats (Float64);
      else
         raise Program_Error;
      end if;
   end MF_Floats;

end Why.Atree.Modules;
