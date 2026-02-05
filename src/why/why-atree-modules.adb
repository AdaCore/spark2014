-----------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - A T R E E - M O D U L E S                   --
--                                                                          --
--                                 B o d Y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
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

with Ada.Characters.Handling;        use Ada.Characters.Handling;
with Ada.Containers;                 use Ada.Containers;
with Ada.Containers.Ordered_Maps;
with Ada.Strings.Unbounded;          use Ada.Strings.Unbounded;
with Errout_Wrapper;                 use Errout_Wrapper;
with Flow_Generated_Globals.Phase_2; use Flow_Generated_Globals.Phase_2;
with Gnat2Why.Tables;                use Gnat2Why.Tables;
with Gnat2Why.Util;                  use Gnat2Why.Util;
with GNATCOLL.Utils;                 use GNATCOLL.Utils;
with SPARK_Definition.Annotate;      use SPARK_Definition.Annotate;
with SPARK_Util.Subprograms;         use SPARK_Util.Subprograms;
with SPARK_Util.Types;               use SPARK_Util.Types;
with Snames;                         use Snames;
with SPARK_Atree;                    use SPARK_Atree;
with SPARK_Util;                     use SPARK_Util;
with Stand;                          use Stand;
with String_Utils;                   use String_Utils;
with Why.Atree.Accessors;            use Why.Atree.Accessors;
with Why.Atree.Builders;             use Why.Atree.Builders;
with Why.Conversions;                use Why.Conversions;
with Why.Gen.Arrays;                 use Why.Gen.Arrays;
with Why.Gen.Init;                   use Why.Gen.Init;
with Why.Gen.Pointers;               use Why.Gen.Pointers;
with Why.Images;                     use Why.Images;
with Why.Inter;                      use Why.Inter;

package body Why.Atree.Modules is

   --  procedures to initialize the various modules

   procedure Init_Boolean_Init_Wrapper_Module;
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
   procedure Init_Int_Gcd_Module;
   procedure Init_Int_Minmax_Module;
   procedure Init_Int_Power_Module;
   procedure Init_Int_Shift_Module;
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

   package Module_Kind_To_Module is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Module_Kind,
        Element_Type => W_Module_Id);

   package Ada_Node_To_Module is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Module_Kind_To_Module.Map,
        Hash            => Node_Hash,
        Equivalent_Keys => "=",
        "="             => Module_Kind_To_Module."=");

   type Why_Symb is record
      Entity : Entity_Id;
      Symb   : Why_Name_Enum;
   end record;

   function Hash (Key : Why_Symb) return Ada.Containers.Hash_Type
   is (3 * Ada.Containers.Hash_Type (Key.Entity)
       + 5 * Ada.Containers.Hash_Type (Why_Name_Enum'Pos (Key.Symb)));

   package Why_Symb_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Why_Symb,
        Element_Type    => W_Identifier_Id,
        Hash            => Hash,
        Equivalent_Keys => "=",
        "="             => "=");

   function Hashconsed_Entity_Module
     (E       : Entity_Id;
      K       : Module_Kind;
      Name    : String;
      Modules : in out Ada_Node_To_Module.Map) return W_Module_Id;
   --  Create a module with name Name and associate it to E in Modules unless
   --  there is already a module associated to E in Modules, in which case the
   --  existing module is returned.

   Why_Symb_Map              : Why_Symb_Maps.Map := Why_Symb_Maps.Empty_Map;
   Why_Relaxed_Symb_Map      : Why_Symb_Maps.Map := Why_Symb_Maps.Empty_Map;
   Entity_Modules            : Ada_Node_To_Module.Map;
   Functions_With_Refinement : Node_Sets.Set;
   Proof_Cyclic_Functions    : Node_Sets.Set;
   Lemmas                    : Node_Sets.Set;

   --------------
   -- E_Module --
   --------------

   function E_Module
     (E : Entity_Id; K : Module_Kind := Regular) return W_Module_Id
   is
      Name : constant String :=
        (if Nkind (E) in N_Entity then Full_Name (E) else "")
        & (case K is
             when Regular                   => "",
             when Axiom                     => "___axiom",
             when Expr_Fun_Axiom            => "___def__axiom",
             when Fun_Post_Axiom            => "___post__axiom",
             when Logic_Function_Decl       => "___logic_fun",
             when Program_Function_Decl     => "___program_fun",
             when Dispatch                  => "___dispatch",
             when Dispatch_Axiom            => "___dispatch__axiom",
             when Dispatch_Post_Axiom       => "___dispatch__post__axiom",
             when Refined_Post_Axiom        => "___refined__post__axiom",
             when Lemma_Axiom               => "___post_axiom",
             when Validity_Wrapper          => "___validity_wrapper",
             when Type_Completion           => "___compl",
             when Type_Representative       => "___rep",
             when Record_Rep_Completion     => "___rep__compl",
             when Init_Wrapper              => "___init_wrapper",
             when Init_Wrapper_Completion   => "___init_wrapper__compl",
             when Init_Wrapper_Pointer_Rep  => "___init_wrapper__rep",
             when Default_Initialialization => "___default_init",
             when Invariant                 => "___invariant",
             when User_Equality             => "___user_eq",
             when User_Equality_Axiom       => "___user_eq__axiom",
             when Dispatch_Equality         => "___dispatch_eq",
             when Dispatch_Equality_Axiom   => "___dispatch_eq__axiom",
             when Move_Tree                 => "___move_tree",
             when Incomp_Move_Tree          => "___incomplete_move_tree",
             when Validity_Tree             => "___validity_tree");

   begin
      --  Sanity checking

      case K is
         when Regular | Axiom
         =>
            null;

         when Expr_Fun_Axiom
         =>
            pragma
              Assert
                (E in Callable_Kind_Id
                 and then Is_Expression_Function_Or_Completion (E)
                 and then Entity_Body_Compatible_With_SPARK (E));

         when Fun_Post_Axiom
         =>
            pragma Assert (E in Callable_Kind_Id);

         when Logic_Function_Decl
         =>
            pragma
              Assert
                (Nkind (E) in N_Aggregate | N_Delta_Aggregate
                 or else
                   (Is_Function_Or_Function_Type (E)
                    and then not Has_Pragma_Volatile_Function (E)
                    and then not Is_Function_With_Side_Effects (E)));

         when Program_Function_Decl
         =>
            pragma
              Assert
                (Nkind (E) in N_Aggregate | N_Delta_Aggregate
                 or else E in Callable_Kind_Id);

         when Dispatch | Dispatch_Axiom | Dispatch_Post_Axiom
         =>
            pragma
              Assert
                (E in Callable_Kind_Id
                 and then Is_Dispatching_Operation (E)
                 and then not Is_Hidden_Dispatching_Operation (E));

         when Refined_Post_Axiom
         =>
            pragma
              Assert
                (E in Callable_Kind_Id
                 and then Entity_Body_In_SPARK (E)
                 and then Has_Contracts (E, Pragma_Refined_Post));

         when Lemma_Axiom
         =>
            pragma Assert (Has_Automatic_Instantiation_Annotation (E));

         when Validity_Wrapper
         =>
            pragma
              Assert (E in Type_Kind_Id and then Type_Might_Be_Invalid (E));

         when Type_Completion | Type_Representative
         =>
            pragma Assert (E in Type_Kind_Id);
            if E in Access_Kind_Id then
               pragma Assert (E = Repr_Pointer_Type (E));
            end if;

         when Record_Rep_Completion
         =>
            pragma Assert (Is_Record_Type_In_Why (E));

         when Init_Wrapper | Init_Wrapper_Completion | Init_Wrapper_Pointer_Rep
         =>
            pragma Assert (E in Type_Kind_Id and then Has_Init_Wrapper (E));
            if K = Init_Wrapper_Pointer_Rep then
               pragma
                 Assert
                   (E in Access_Kind_Id and then E = Repr_Pointer_Type (E));
            end if;

         when Default_Initialialization
         =>
            pragma
              Assert
                (E in Type_Kind_Id
                 and then not Is_Itype (E)
                 and then Can_Be_Default_Initialized (E));

         when Invariant
         =>
            pragma
              Assert (E in Type_Kind_Id and then Has_Invariants_In_SPARK (E));

         when User_Equality | User_Equality_Axiom
         =>
            pragma
              Assert
                (E in Type_Kind_Id
                 and then not Use_Predefined_Equality_For_Type (E));

         when Dispatch_Equality | Dispatch_Equality_Axiom
         =>
            pragma Assert (Is_Tagged_Type (E) and then E = Root_Retysp (E));

         when Move_Tree | Incomp_Move_Tree
         =>
            pragma
              Assert (E in Type_Kind_Id and then Contains_Allocated_Parts (E));

         when Validity_Tree
         =>
            pragma
              Assert
                (E in Type_Kind_Id
                 and then not Is_Scalar_Type (E)
                 and then Type_Might_Be_Invalid (E)
                 and then E = Base_Retysp (E));
      end case;

      return Hashconsed_Entity_Module (E, K, Name, Entity_Modules);
   end E_Module;

   ------------
   -- E_Symb --
   ------------

   function E_Symb
     (E : Entity_Id; S : Why_Name_Enum; Relaxed_Init : Boolean := False)
      return W_Identifier_Id
   is
      use Why_Symb_Maps;
      E2  : constant Entity_Id := (if Is_Type (E) then Retysp (E) else E);
      Key : constant Why_Symb := Why_Symb'(Entity => E2, Symb => S);
      C   : constant Why_Symb_Maps.Cursor :=
        (if Relaxed_Init
         then Why_Relaxed_Symb_Map.Find (Key)
         else Why_Symb_Map.Find (Key));
   begin
      return Id : W_Identifier_Id do
         if Has_Element (C) then
            Id := Element (C);
         else
            Insert_Why_Symbols (E2);

            if Relaxed_Init then
               Id := Why_Relaxed_Symb_Map.Element (Key);
            else
               Id := Why_Symb_Map.Element (Key);
            end if;
         end if;
      end return;
   end E_Symb;

   ------------------------
   -- Get_Logic_Function --
   ------------------------

   function Get_Logic_Function (E : Function_Kind_Id) return W_Identifier_Id is
      Name : constant Symbol := Get_Profile_Theory_Name (E);
   begin
      return M_Subprogram_Profiles (Name).Call_Id;
   end Get_Logic_Function;

   ------------------------------
   -- Get_Logic_Function_Guard --
   ------------------------------

   function Get_Logic_Function_Guard
     (E : Function_Kind_Id) return W_Identifier_Id
   is
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
      Name      : Unbounded_String := To_Unbounded_String ("profile");
      Type_Name : Unbounded_String;
      Mode_Name : Unbounded_String;
      Param     : Entity_Id := First_Formal (E);
   begin
      while Present (Param) loop
         Mode_Name :=
           To_Unbounded_String
             (case Formal_Kind (Ekind (Param)) is
                when E_In_Parameter     => "__In",
                when E_Out_Parameter    => "__Out",
                when E_In_Out_Parameter => "__InOut");
         Type_Name :=
           To_Unbounded_String
             ("__" & Capitalize_First (Full_Name (Retysp (Etype (Param)))));

         Name := Name & Mode_Name & Type_Name;

         Next_Formal (Param);
      end loop;

      if Is_Function_Or_Function_Type (E) then
         Type_Name :=
           (To_Unbounded_String
              ("__Return__"
               & Capitalize_First (Full_Name (Retysp (Etype (E))))));
         Name := Name & Type_Name;
      end if;

      return NID (To_String (Name));
   end Get_Profile_Theory_Name;

   ------------------------
   -- Get_Move_Tree_Type --
   ------------------------

   function Get_Move_Tree_Type (E : Entity_Id) return W_Type_Id is
   begin
      return
        New_Named_Type
          (Name =>
             New_Name
               (Symb   => NID (To_String (WNE_Move_Tree)),
                Module => E_Module (Retysp (E), Move_Tree)));
   end Get_Move_Tree_Type;

   -------------------------
   -- Get_Refinement_Mask --
   -------------------------

   function Get_Refinement_Mask (E : Entity_Id) return Why_Node_Maps.Map is
   begin
      return Res : Why_Node_Maps.Map do
         for F of Functions_With_Refinement loop
            declare
               Visible : constant Boolean := Has_Visibility_On_Refined (E, F);
            begin
               --  If the refinement of F is visible from E, replace its post
               --  axiom by its refined post axiom.

               if Entity_Modules (F).Contains (Refined_Post_Axiom)
                 and then Visible
               then
                  Res.Insert
                    (+E_Module (F, Fun_Post_Axiom),
                     +E_Module (F, Refined_Post_Axiom));
               end if;

               --  If the refinement of an expression function F is not visible
               --  from E, remove its defining axiom.

               if Entity_Modules (F).Contains (Expr_Fun_Axiom)
                 and then not Visible
               then
                  Res.Insert (+E_Module (F, Expr_Fun_Axiom), Why_Empty);
               end if;
            end;
         end loop;
      end return;
   end Get_Refinement_Mask;

   ----------------------------
   -- Get_Validity_Tree_Type --
   ----------------------------

   function Get_Validity_Tree_Type (E : Entity_Id) return W_Type_Id is
      Rep_Ty : constant Type_Kind_Id := Retysp (E);

   begin
      if Is_Scalar_Type (Rep_Ty) then
         return EW_Bool_Type;
      else
         return
           New_Named_Type
             (Name =>
                New_Name
                  (Symb   => NID (To_String (WNE_Validity_Tree)),
                   Module => E_Module (Base_Retysp (Rep_Ty), Validity_Tree)));
      end if;
   end Get_Validity_Tree_Type;

   ------------------------------
   -- Hashconsed_Entity_Module --
   ------------------------------

   function Hashconsed_Entity_Module
     (E       : Entity_Id;
      K       : Module_Kind;
      Name    : String;
      Modules : in out Ada_Node_To_Module.Map) return W_Module_Id
   is
      use Module_Kind_To_Module;
      Normalized_E : constant Entity_Id :=
        (if Nkind (E) in N_Entity
           and then Ekind (E) = E_Constant
           and then Is_Partial_View (E)
           and then Entity_In_SPARK (Full_View (E))
         then Full_View (E)
         else E);
      --  For constants, use the entity of the full view if it is in SPARK
      Position     : Ada_Node_To_Module.Cursor;
      Inserted     : Boolean;
      C            : Module_Kind_To_Module.Cursor := No_Element;
   begin
      Modules.Insert (Normalized_E, Empty_Map, Position, Inserted);

      if not Inserted then
         C := Modules (Position).Find (K);
      end if;

      if Has_Element (C) then
         return Element (C);
      elsif Nkind (E) in N_Entity then
         declare
            M : constant W_Module_Id :=
              New_Module
                (Ada_Node => Normalized_E, File => No_Symbol, Name => Name);
         begin
            Modules (Position).Insert (K, M);
            return M;
         end;
      else
         return Why_Empty;
      end if;
   end Hashconsed_Entity_Module;

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      --  Initialize files first

      Int_File := NID ("int");
      Real_File := NID ("real");
      Ref_File := NID ("ref");

      Gnatprove_Standard_File := NID ("_gnatprove_standard");
      Ada_Model_File := NID ("ada__model");

      --  Modules of the Why standard library

      Int_Module := New_Module (File => Int_File, Name => "Int");
      RealInfix := New_Module (File => Real_File, Name => "RealInfix");
      Ref_Module := New_Module (File => Ref_File, Name => "Ref");

      --  Builtin Why types

      EW_Bool_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("bool")),
           Is_Mutable => False);
      EW_Int_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("int")),
           Is_Mutable => False);
      EW_Prop_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("prop")),
           Is_Mutable => False);
      EW_Real_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("real")),
           Is_Mutable => False);
      EW_Unit_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("unit")),
           Is_Mutable => False);

      --  built-in void ident

      Init_Main_Module;
      Init_Boolean_Init_Wrapper_Module;
      Init_Compat_Tags_Module;
      Init_Integer_Module;
      Init_Int_Power_Module;
      Init_Int_Shift_Module;
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
        New_Module (File => Ada_Model_File, Name => "Static_Modular_lt8");
      Static_Modular_lt16 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_lt16");
      Static_Modular_lt32 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_lt32");
      Static_Modular_lt64 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_lt64");
      Static_Modular_lt128 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_lt128");
      Static_Modular_8 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_8");
      Static_Modular_16 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_16");
      Static_Modular_32 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_32");
      Static_Modular_64 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_64");
      Static_Modular_128 :=
        New_Module (File => Ada_Model_File, Name => "Static_Modular_128");
      Static_Discrete :=
        New_Module (File => Ada_Model_File, Name => "Static_Discrete");
      Dynamic_Modular :=
        New_Module (File => Ada_Model_File, Name => "Dynamic_Modular");
      Dynamic_Discrete :=
        New_Module (File => Ada_Model_File, Name => "Dynamic_Discrete");
      Static_Fixed_Point :=
        New_Module (File => Ada_Model_File, Name => "Static_Fixed_Point");
      Dynamic_Fixed_Point :=
        New_Module (File => Ada_Model_File, Name => "Dynamic_Fixed_Point");
      Fixed_Point_Rep :=
        New_Module (File => Ada_Model_File, Name => "Fixed_Point_Rep");
      Fixed_Point_Mult_Div :=
        New_Module (File => Ada_Model_File, Name => "Fixed_Point_Mult_Div");
      Static_Float32 :=
        New_Module (File => Ada_Model_File, Name => "Static_Float32");
      Static_Float64 :=
        New_Module (File => Ada_Model_File, Name => "Static_Float64");
      Static_Float80 :=
        New_Module (File => Ada_Model_File, Name => "Static_Float80");
      Dynamic_Float :=
        New_Module (File => Ada_Model_File, Name => "Dynamic_Floating_Point");
      Rep_Proj_Float32 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_Float32");
      Rep_Proj_Float64 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_Float64");
      Rep_Proj_Float80 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_Float80");
      Rep_Proj_Fixed :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_Fixed");
      Rep_Proj_Int :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_Int");
      Rep_Proj_Lt8 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_ltBV8");
      Rep_Proj_Lt16 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_ltBV16");
      Rep_Proj_Lt32 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_ltBV32");
      Rep_Proj_Lt64 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_ltBV64");
      Rep_Proj_Lt128 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_ltBV128");
      Rep_Proj_8 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_BV8");
      Rep_Proj_16 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_BV16");
      Rep_Proj_32 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_BV32");
      Rep_Proj_64 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_BV64");
      Rep_Proj_128 :=
        New_Module (File => Ada_Model_File, Name => "Rep_Proj_BV128");
      Incomp_Ty_Conv :=
        New_Module (File => Ada_Model_File, Name => "Incomplete_type");
      Pledge := New_Module (File => Ada_Model_File, Name => "Pledge");
      Real_Time_Model :=
        New_Module (File => Ada_Model_File, Name => "Real_time__model");

      Constr_Arrays :=
        (1 => New_Module (File => Ada_Model_File, Name => "Constr_Array"),
         2 => New_Module (File => Ada_Model_File, Name => "Constr_Array_2"),
         3 => New_Module (File => Ada_Model_File, Name => "Constr_Array_3"),
         4 => New_Module (File => Ada_Model_File, Name => "Constr_Array_4"));
      Unconstr_Arrays :=
        (1 => New_Module (File => Ada_Model_File, Name => "Unconstr_Array"),
         2 => New_Module (File => Ada_Model_File, Name => "Unconstr_Array_2"),
         3 => New_Module (File => Ada_Model_File, Name => "Unconstr_Array_3"),
         4 => New_Module (File => Ada_Model_File, Name => "Unconstr_Array_4"));

      Array_Int_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Array_Int_Rep_Comparison_Axiom");

      Array_BV8_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Array_BV8_Rep_Comparison_Axiom");

      Array_BV16_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Array_BV16_Rep_Comparison_Axiom");

      Array_BV32_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Array_BV32_Rep_Comparison_Axiom");

      Array_BV64_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Array_BV64_Rep_Comparison_Axiom");

      Array_BV128_Rep_Comparison_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Array_BV128_Rep_Comparison_Axiom");

      Standard_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Standard_Array_Logical_Op_Axioms");

      Subtype_Array_Logical_Ax :=
        New_Module
          (File => Ada_Model_File, Name => "Subtype_Array_Logical_Op_Axioms");

      --  Builtin unary minus and void

      Int_Unary_Minus :=
        New_Identifier
          (Domain => EW_Term, Symb => NID ("-"), Typ => EW_Int_Type);
      Fixed_Unary_Minus :=
        New_Identifier
          (Domain => EW_Term, Symb => NID ("-"), Typ => M_Main.Fixed_Type);
      Real_Unary_Minus :=
        New_Identifier
          (Domain => EW_Term, Symb => NID ("-."), Typ => EW_Real_Type);

      Void :=
        New_Identifier
          (Domain => EW_Term, Symb => NID ("()"), Typ => EW_Unit_Type);

      --  Builtin infix operations

      Why_Eq :=
        New_Identifier
          (Domain => EW_Term,
           Symb   => NID ("="),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Why_Neq :=
        New_Identifier
          (Domain => EW_Term,
           Symb   => NID ("<>"),
           Typ    => EW_Bool_Type,
           Infix  => True);

      Int_Infix_Add :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("+"),
           Typ    => EW_Int_Type,
           Infix  => True);
      Int_Infix_Subtr :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("-"),
           Typ    => EW_Int_Type,
           Infix  => True);
      Int_Infix_Mult :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("*"),
           Typ    => EW_Int_Type,
           Infix  => True);
      Int_Infix_Le :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("<="),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Int_Infix_Lt :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("<"),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Int_Infix_Ge :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID (">="),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Int_Infix_Gt :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID (">"),
           Typ    => EW_Bool_Type,
           Infix  => True);

      Fixed_Infix_Add :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("+"),
           Typ    => M_Main.Fixed_Type,
           Infix  => True);
      Fixed_Infix_Subtr :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("-"),
           Typ    => M_Main.Fixed_Type,
           Infix  => True);
      Fixed_Infix_Mult :=
        New_Identifier
          (Module => Int_Module,
           Domain => EW_Term,
           Symb   => NID ("*"),
           Typ    => M_Main.Fixed_Type,
           Infix  => True);

      Real_Infix_Add :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID ("+."),
           Typ    => EW_Real_Type,
           Infix  => True);
      Real_Infix_Subtr :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID ("-."),
           Typ    => EW_Real_Type,
           Infix  => True);
      Real_Infix_Mult :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID ("*."),
           Typ    => EW_Real_Type,
           Infix  => True);
      Real_Infix_Div :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID ("/."),
           Typ    => EW_Real_Type,
           Infix  => True);
      Real_Infix_Le :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID ("<=."),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Real_Infix_Lt :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID ("<."),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Real_Infix_Ge :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID (">=."),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Real_Infix_Gt :=
        New_Identifier
          (Module => RealInfix,
           Domain => EW_Term,
           Symb   => NID (">."),
           Typ    => EW_Bool_Type,
           Infix  => True);
      Real_Infix_Eq :=
        New_Identifier
          (Module => RealInfix,
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
        New_Identifier
          (Ada_Node => Standard_String,
           Domain   => EW_Term,
           Module   => String_Image_Module,
           Symb     => NID ("to_string"));

      Of_String_Id :=
        New_Identifier
          (Ada_Node => Standard_String,
           Domain   => EW_Term,
           Module   => String_Image_Module,
           Symb     => NID ("from_string"));

      --  Module for overflow checks for Unsigned_Base_Range integers in
      --  minimized mode

      Unsigned_Base_Range_Overflow_Module :=
        New_Module
          (Ada_Node => Empty,
           File     => No_Symbol,
           Name     => "Standard_Long_Long_Unsigned__Unsigned_Base_Range");

      Unsigned_Base_Range_Overflow_Check :=
        New_Identifier
          (Ada_Node => Standard_Long_Long_Unsigned,
           Domain   => EW_Prog,
           Module   => Unsigned_Base_Range_Overflow_Module,
           Symb     => NID ("unsigned_base_range_minimized_overflow_check"));

      --  Other identifiers

      Old_Tag := NID ("old");
      Def_Name := New_Identifier (Symb => NID ("def"), Domain => EW_Term);

      --  Modules of _gnatprove_standard file

      Array_Modules :=
        (1 => New_Module (File => Gnatprove_Standard_File, Name => "Array__1"),
         2 => New_Module (File => Gnatprove_Standard_File, Name => "Array__2"),
         3 => New_Module (File => Gnatprove_Standard_File, Name => "Array__3"),
         4 =>
           New_Module (File => Gnatprove_Standard_File, Name => "Array__4"));

      --  Generated specific modules

      Exception_Module :=
        New_Module
          (File => GNATCOLL.Symbols.No_Symbol,
           Name => "Standard__ada_exceptions");
   end Initialize;

   -----------------------
   -- Init_Array_Module --
   -----------------------

   function Init_Array_Module (Module : W_Module_Id) return M_Array_Type is
      M_Array : M_Array_Type;
      Ty      : constant W_Type_Id :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("map"), Module => Module),
           Is_Mutable => False);
      Comp_Ty : constant W_Type_Id :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       =>
             New_Name (Symb => NID ("component_type"), Module => Module),
           Is_Mutable => False);
   begin
      M_Array.Module := Module;

      M_Array.Ty := Ty;
      M_Array.Comp_Ty := Comp_Ty;
      M_Array.Get :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("get"),
           Typ    => Comp_Ty);
      M_Array.Set :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("set"),
           Typ    => Ty);
      M_Array.Bool_Eq :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("bool_eq"),
           Typ    => EW_Bool_Type);
      M_Array.Slide :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("slide"),
           Typ    => Ty);
      M_Array.Const :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("const"),
           Typ    => Ty);
      M_Array.Slice :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("slice"),
           Typ    => Ty);

      return M_Array;
   end Init_Array_Module;

   -------------------------
   -- Init_Array_1_Module --
   -------------------------

   function Init_Array_1_Module (Module : W_Module_Id) return M_Array_1_Type is
      M_Array_1 : M_Array_1_Type;
      Ty        : constant W_Type_Id :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("map"), Module => Module),
           Is_Mutable => False);
   begin
      M_Array_1.Module := Module;
      M_Array_1.Concat :=
        (False =>
           (False =>
              New_Identifier
                (Module => Module,
                 Domain => EW_Term,
                 Symb   => NID ("concat"),
                 Typ    => Ty),
            True  =>
              New_Identifier
                (Module => Module,
                 Domain => EW_Term,
                 Symb   => NID ("concat_singleton_right"),
                 Typ    => Ty)),
         True  =>
           (False =>
              New_Identifier
                (Module => Module,
                 Domain => EW_Term,
                 Symb   => NID ("concat_singleton_left"),
                 Typ    => Ty),
            True  =>
              New_Identifier
                (Module => Module,
                 Domain => EW_Term,
                 Symb   => NID ("concat_singletons"),
                 Typ    => Ty)));
      M_Array_1.Singleton :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("singleton"),
           Typ    => Ty);

      return M_Array_1;
   end Init_Array_1_Module;

   ------------------------------
   -- Init_Array_1_Comp_Module --
   ------------------------------

   function Init_Array_1_Comp_Module
     (Module : W_Module_Id) return M_Array_1_Comp_Type
   is
      M_Array_1 : M_Array_1_Comp_Type;

   begin
      M_Array_1.Module := Module;
      M_Array_1.Compare :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("compare"),
           Typ    => EW_Int_Type);

      return M_Array_1;
   end Init_Array_1_Comp_Module;

   function Init_Array_1_Bool_Op_Module
     (Module : W_Module_Id) return M_Array_1_Bool_Op_Type
   is
      M_Array_1 : M_Array_1_Bool_Op_Type;
      Ty        : constant W_Type_Id :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("map"), Module => Module),
           Is_Mutable => False);

   begin
      M_Array_1.Module := Module;
      M_Array_1.Xorb :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("xorb"),
           Typ    => Ty);
      M_Array_1.Andb :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("andb"),
           Typ    => Ty);
      M_Array_1.Orb :=
        New_Identifier
          (Module => Module,
           Domain => EW_Term,
           Symb   => NID ("orb"),
           Typ    => Ty);
      M_Array_1.Notb :=
        New_Identifier
          (Module => Module,
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
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_eq"),
           Typ    => EW_Bool_Type);
      M_Boolean.Bool_Ne :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_ne"),
           Typ    => EW_Bool_Type);
      M_Boolean.Bool_Le :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_le"),
           Typ    => EW_Bool_Type);
      M_Boolean.Bool_Lt :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_lt"),
           Typ    => EW_Bool_Type);
      M_Boolean.Bool_Ge :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_ge"),
           Typ    => EW_Bool_Type);
      M_Boolean.Bool_Gt :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_gt"),
           Typ    => EW_Bool_Type);
      M_Boolean.Notb :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("notb"),
           Typ    => EW_Bool_Type);
      M_Boolean.Andb :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("andb"),
           Typ    => EW_Bool_Type);
      M_Boolean.Notb :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("notb"),
           Typ    => EW_Bool_Type);
      M_Boolean.Orb :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("orb"),
           Typ    => EW_Bool_Type);
      M_Boolean.Xorb :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("xorb"),
           Typ    => EW_Bool_Type);
      M_Boolean.To_Int :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("to_int"),
           Typ    => EW_Int_Type);
      M_Boolean.Of_Int :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("of_int"),
           Typ    => EW_Bool_Type);
      M_Boolean.Range_Check :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("range_check_"),
           Typ    => EW_Int_Type);
      M_Boolean.Check_Not_First :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("check_not_first"),
           Typ    => EW_Int_Type);
      M_Boolean.Check_Not_Last :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("check_not_last"),
           Typ    => EW_Int_Type);
      M_Boolean.First :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("first"),
           Typ    => EW_Int_Type);
      M_Boolean.Last :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("last"),
           Typ    => EW_Int_Type);
      M_Boolean.Range_Pred :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("in_range"),
           Typ    => EW_Bool_Type);
      M_Boolean.Dynamic_Prop :=
        New_Identifier
          (Module => M,
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
        New_Module
          (File => Gnatprove_Standard_File, Name => "Builtin_from_image");
   begin
      M_Builtin_From_Image.Int_Value :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("int__attr__ATTRIBUTE_VALUE"),
           Typ    => EW_Int_Type);

      M_Builtin_From_Image.Real_Value :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("real__attr__ATTRIBUTE_VALUE"),
           Typ    => EW_Real_Type);

      M_Builtin_From_Image.Real_Quotient_Value :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("real__QUOTIENT_VALUE"),
           Typ    => EW_Real_Type);

   end Init_Builtin_From_Image_Module;

   --------------------------
   -- Init_BV_Conv_Modules --
   --------------------------

   procedure Init_BV_Conv_Modules is
      M : W_Module_Id;
   begin
      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_128_256");
      M_BV_Conv_128_256 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_256_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_128_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_256_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_64_128");
      M_BV_Conv_64_128 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_128_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_64_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_128_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_32_128");
      M_BV_Conv_32_128 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_128_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_32_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_128_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_16_128");
      M_BV_Conv_16_128 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_128_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_16_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_128_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_8_128");
      M_BV_Conv_8_128 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_128_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_8_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_128_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_32_64");
      M_BV_Conv_32_64 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_64_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_32_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_64_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_16_64");
      M_BV_Conv_16_64 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_64_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_16_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_64_Type));

      M := New_Module (File => Gnatprove_Standard_File, Name => "BVConv_8_64");
      M_BV_Conv_8_64 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_64_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_8_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_64_Type));

      M :=
        New_Module (File => Gnatprove_Standard_File, Name => "BVConv_16_32");
      M_BV_Conv_16_32 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_32_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_16_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_32_Type));

      M := New_Module (File => Gnatprove_Standard_File, Name => "BVConv_8_32");
      M_BV_Conv_8_32 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_32_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_8_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_BitVector_32_Type));

      M := New_Module (File => Gnatprove_Standard_File, Name => "BVConv_8_16");
      M_BV_Conv_8_16 :=
        M_BV_Conv_Type'
          (Module      => M,
           To_Big      =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toBig"),
                Typ    => EW_BitVector_16_Type),
           To_Small    =>
             New_Identifier
               (Module => M,
                Domain => EW_Term,
                Symb   => NID ("toSmall"),
                Typ    => EW_BitVector_8_Type),
           Range_Check =>
             New_Identifier
               (Module => M,
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
        New_Module (File => Gnatprove_Standard_File, Name => "BV8");
      M_BVs (BV16).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "BV16");
      M_BVs (BV32).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "BV32");
      M_BVs (BV64).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "BV64");
      M_BVs (BV128).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "BV128");
      M_BVs (BV256).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "BV256");

      for BV in BV_Kind loop
         M_BVs (BV).T :=
           New_Type
             (Type_Kind  => EW_Builtin,
              Name       =>
                New_Name (Symb => NID ("t"), Module => M_BVs (BV).Module),
              Is_Mutable => False);
         M_BVs (BV).Ult :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("ult"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Ule :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("ule"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Ugt :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("ugt"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Uge :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("uge"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).BV_Min :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bv_min"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).BV_Max :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bv_max"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Bool_Eq :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bool_eq"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Ne :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bool_ne"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Le :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bool_le"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Lt :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bool_lt"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Ge :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bool_ge"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).Bool_Gt :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bool_gt"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Bool_Type);
         M_BVs (BV).One :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("one"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Add :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("add"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Sub :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("sub"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Neg :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("neg"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Mult :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("mul"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Power :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("power"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Udiv :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("udiv"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Urem :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("urem"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Urem :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("urem"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_And :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bw_and"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Or :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bw_or"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Xor :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bw_xor"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).BW_Not :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("bw_not"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).BV_Abs :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("abs"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsl :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("lsl_bv"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Lsr :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("lsr_bv"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Asr :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("asr_bv"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Rotate_Left :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("rotate_left_bv"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Rotate_Right :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("rotate_right_bv"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).Of_Int :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("of_int"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).To_Int :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("t_int"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Int_Type);
         M_BVs (BV).UC_Of_Int :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("uc_of_int"),
              Module => M_BVs (BV).Module,
              Typ    => M_BVs (BV).T);
         M_BVs (BV).UC_To_Int :=
           New_Identifier
             (Domain => EW_Term,
              Symb   => NID ("uc_to_int"),
              Module => M_BVs (BV).Module,
              Typ    => EW_Int_Type);
         M_BVs (BV).Two_Power_Size :=
           New_Identifier
             (Module => M_BVs (BV).Module,
              Domain => EW_Term,
              Symb   => NID ("_two_power_size"),
              Typ    => EW_Int_Type);
         M_BVs (BV).Prog_Eq :=
           New_Identifier
             (Module => M_BVs (BV).Module,
              Domain => EW_Term,
              Symb   => NID ("eq"),
              Typ    => EW_Bool_Type);
         M_BVs (BV).Prog_Neq :=
           New_Identifier
             (Module => M_BVs (BV).Module,
              Domain => EW_Term,
              Symb   => NID ("neq"),
              Typ    => EW_Bool_Type);
      end loop;

      EW_BitVector_8_Type := M_BVs (BV8).T;
      EW_BitVector_16_Type := M_BVs (BV16).T;
      EW_BitVector_32_Type := M_BVs (BV32).T;
      EW_BitVector_64_Type := M_BVs (BV64).T;
      EW_BitVector_128_Type := M_BVs (BV128).T;
      EW_BitVector_256_Type := M_BVs (BV256).T;
   end Init_BV_Modules;

   --------------------------------------
   -- Init_Boolean_Init_Wrapper_Module --
   --------------------------------------

   procedure Init_Boolean_Init_Wrapper_Module is
      M : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Boolean__init_wrapper");
   begin
      M_Boolean_Init_Wrapper.Module := M;
      M_Boolean_Init_Wrapper.Wrapper_Ty :=
        New_Type
          (Type_Kind    => EW_Builtin,
           Name         =>
             New_Name (Symb => NID ("boolean__init_wrapper"), Module => M),
           Relaxed_Init => True,
           Is_Mutable   => False);
      M_Boolean_Init_Wrapper.Of_Wrapper :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("of_wrapper"),
           Typ    => EW_Bool_Type);
      M_Boolean_Init_Wrapper.To_Wrapper :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("to_wrapper"),
           Typ    => M_Boolean_Init_Wrapper.Wrapper_Ty);
      M_Boolean_Init_Wrapper.Attr_Init :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("__attr__init"),
           Typ    => EW_Bool_Type);
   end Init_Boolean_Init_Wrapper_Module;

   -----------------------------
   -- Init_Compat_Tags_Module --
   -----------------------------

   procedure Init_Compat_Tags_Module is
      M : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Compatible_Tags");
   begin
      M_Compat_Tags.Module := M;
      M_Compat_Tags.Compat_Tags_Id :=
        New_Identifier
          (Domain => EW_Pred,
           Module => M,
           Symb   => NID ("__compatible_tags"),
           Typ    => EW_Bool_Type);
   end Init_Compat_Tags_Module;

   -------------------------------
   -- Init_Floating_Conv_Module --
   -------------------------------

   procedure Init_Floating_Conv_Module is
      Float32_64_Conv : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float32_64_Converter");
      Float32_80_Conv : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float32_80_Converter");
      Float64_80_Conv : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float64_80_Converter");
   begin
      M_Float32_64_Conv :=
        M_Floating_Conv_Type'
          (Module      => Float32_64_Conv,
           To_Large    =>
             New_Identifier
               (Module => Float32_64_Conv,
                Domain => EW_Term,
                Symb   => NID ("to_float64_rne"),
                Typ    => EW_Float_64_Type),
           To_Small    =>
             New_Identifier
               (Module => Float32_64_Conv,
                Domain => EW_Term,
                Symb   => NID ("to_float32_rne"),
                Typ    => EW_Float_32_Type),
           Range_Check =>
             New_Identifier
               (Module => Float32_64_Conv,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_Float_64_Type));
      M_Float32_80_Conv :=
        M_Floating_Conv_Type'
          (Module      => Float32_80_Conv,
           To_Large    =>
             New_Identifier
               (Module => Float32_80_Conv,
                Domain => EW_Term,
                Symb   => NID ("to_float80_rne"),
                Typ    => EW_Float_80_Type),
           To_Small    =>
             New_Identifier
               (Module => Float32_80_Conv,
                Domain => EW_Term,
                Symb   => NID ("to_float32_rne"),
                Typ    => EW_Float_32_Type),
           Range_Check =>
             New_Identifier
               (Module => Float32_80_Conv,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_Float_80_Type));
      M_Float64_80_Conv :=
        M_Floating_Conv_Type'
          (Module      => Float64_80_Conv,
           To_Large    =>
             New_Identifier
               (Module => Float64_80_Conv,
                Domain => EW_Term,
                Symb   => NID ("to_float80_rne"),
                Typ    => EW_Float_80_Type),
           To_Small    =>
             New_Identifier
               (Module => Float64_80_Conv,
                Domain => EW_Term,
                Symb   => NID ("to_float64_rne"),
                Typ    => EW_Float_64_Type),
           Range_Check =>
             New_Identifier
               (Module => Float64_80_Conv,
                Domain => EW_Term,
                Symb   => NID ("range_check_"),
                Typ    => EW_Float_80_Type));
   end Init_Floating_Conv_Module;

   --------------------------
   -- Init_Floating_Module --
   --------------------------

   procedure Init_Floating_Module is
      Float32_BV_Converter : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float32_BV_Converter");
      Float64_BV_Converter : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float64_BV_Converter");
      Float80_BV_Converter : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float80_BV_Converter");
   begin
      M_Floats (Float32).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "Float32");
      M_Floats (Float64).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "Float64");
      M_Floats (Float80).Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "Float80");
      M_Floats (Float32).Power_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "Float32_power");
      M_Floats (Float64).Power_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "Float64_power");
      M_Floats (Float80).Power_Module :=
        New_Module (File => Gnatprove_Standard_File, Name => "Float80_power");
      M_Floats (Float32).Next_Prev_Module :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float32_next_prev");
      M_Floats (Float64).Next_Prev_Module :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float64_next_prev");
      M_Floats (Float80).Next_Prev_Module :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float80_next_prev");
      M_Floats (Float32).Operations_Module :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float32_operations");
      M_Floats (Float64).Operations_Module :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float64_operations");
      M_Floats (Float80).Operations_Module :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Float80_operations");

      for Fl in Floating_Kind loop
         M_Floats (Fl).T :=
           New_Type
             (Type_Kind  => EW_Builtin,
              Name       =>
                New_Name (Symb => NID ("t"), Module => M_Floats (Fl).Module),
              Is_Mutable => False);
         M_Floats (Fl).Bool_Eq :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("bool_eq"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Ne :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("bool_neq"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Le :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("bool_le"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Lt :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("bool_lt"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Ge :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("bool_ge"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Bool_Gt :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("bool_gt"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Max :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("max"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Min :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("min"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Abs_Float :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("abs"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Ceil :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("ceil"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Floor :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("floor"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Is_Finite :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("t'isFinite"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Power :=
           New_Identifier
             (Module => M_Floats (Fl).Power_Module,
              Domain => EW_Term,
              Symb   => NID ("power"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).To_Int :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("to_int_rna"),
              Typ    => EW_Int_Type);
         M_Floats (Fl).Rounding :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("rounding"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Of_Int :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("of_int_rne"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Truncate :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("truncate"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Unary_Minus :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("neg"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Add :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("add_rne"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Subtr :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("sub_rne"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Mult :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("mul_rne"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Div :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("div_rne"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Remainder :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("rem"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Le :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("le"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Lt :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("lt"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Ge :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("ge"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Gt :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("gt"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Eq :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("eq"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Neq :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("neq"),
              Typ    => EW_Bool_Type);
         M_Floats (Fl).Prev_Rep :=
           New_Identifier
             (Module => M_Floats (Fl).Next_Prev_Module,
              Domain => EW_Term,
              Symb   => NID ("prev_representable"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Next_Rep :=
           New_Identifier
             (Module => M_Floats (Fl).Next_Prev_Module,
              Domain => EW_Term,
              Symb   => NID ("next_representable"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Plus_Zero :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("_zeroF"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).One :=
           New_Identifier
             (Module => M_Floats (Fl).Module,
              Domain => EW_Term,
              Symb   => NID ("one"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Ada_Power :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("ada_power"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Ada_Power_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("ada_power_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Ada_Sqrt :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("ada_sqrt"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Log :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("log"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Log_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("log_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Log_Base :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("log_base"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Log_Base_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("log_base_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Exp :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("exp"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Sin :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("sin"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cos :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cos"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Tan :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("tan"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cot :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cot"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cot_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cot_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arcsin :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arcsin"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccos :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccos"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arctan :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arctan"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccot :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccot"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Sin_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("sin_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cos_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cos_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Tan_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("tan_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Tan_2_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("tan_2_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cot_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cot_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cot_2_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cot_2_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arcsin_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arcsin_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccos_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccos_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arctan_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arctan_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccot_2 :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccot_2"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Sinh :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("sinh"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Cosh :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("cosh"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Tanh :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("tanh"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Coth :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("coth"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Coth_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("coth_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arcsinh :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arcsinh"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccosh :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccosh"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccosh_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccosh_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arctanh :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arctanh"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arctanh_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arctanh_definition_domain"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccoth :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccoth"),
              Typ    => M_Floats (Fl).T);
         M_Floats (Fl).Arccoth_Definition_Domain :=
           New_Identifier
             (Module => M_Floats (Fl).Operations_Module,
              Domain => EW_Term,
              Symb   => NID ("arccoth_definition_domain"),
              Typ    => M_Floats (Fl).T);
         declare
            Float_Converter : constant W_Module_Id :=
              (case Fl is
                 when Float32 => Float32_BV_Converter,
                 when Float64 => Float64_BV_Converter,
                 when Float80 => Float80_BV_Converter);
         begin
            M_Floats (Fl).Of_BV8 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv8_rne"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV16 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv16_rne"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV32 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv32_rne"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV64 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv64_rne"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV8_RTN :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv8_rtn"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV16_RTN :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv16_rtn"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV32_RTN :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv32_rtn"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV64_RTN :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv64_rtn"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV8_RTP :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv8_rtp"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV16_RTP :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv16_rtp"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV32_RTP :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv32_rtp"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).Of_BV64_RTP :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("of_ubv64_rtp"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).To_BV8 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("to_ubv8_rna"),
                 Typ    => EW_BitVector_8_Type);
            M_Floats (Fl).To_BV16 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("to_ubv16_rna"),
                 Typ    => EW_BitVector_16_Type);
            M_Floats (Fl).To_BV32 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("to_ubv32_rna"),
                 Typ    => EW_BitVector_32_Type);
            M_Floats (Fl).To_BV64 :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("to_ubv64_rna"),
                 Typ    => EW_BitVector_64_Type);
            M_Floats (Fl).Range_Check :=
              New_Identifier
                (Module => Float_Converter,
                 Domain => EW_Term,
                 Symb   => NID ("range_check_"),
                 Typ    => M_Floats (Fl).T);
            M_Floats (Fl).To_Real :=
              New_Identifier
                (Module => M_Floats (Fl).Module,
                 Domain => EW_Term,
                 Symb   => NID ("to_real"),
                 Typ    => EW_Int_Type);
            M_Floats (Fl).Copy_Sign :=
              New_Identifier
                (Module => M_Floats (Fl).Module,
                 Domain => EW_Term,
                 Symb   => NID ("copy_sign"),
                 Typ    => M_Floats (Fl).T);
         end;
      end loop;

      EW_Float_32_Type := M_Floats (Float32).T;
      EW_Float_64_Type := M_Floats (Float64).T;
      EW_Float_80_Type := M_Floats (Float80).T;
   end Init_Floating_Module;

   -------------------------
   -- Init_Int_Abs_Module --
   -------------------------

   procedure Init_Int_Abs_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Int_Abs");
   begin
      M_Int_Abs.Module := M;
      M_Int_Abs.Abs_Id :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("abs"),
           Typ    => EW_Int_Type);
   end Init_Int_Abs_Module;

   -------------------------
   -- Init_Int_Div_Module --
   -------------------------

   procedure Init_Int_Div_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Int_Division");
   begin
      M_Int_Div.Module := M;
      M_Int_Div.Div :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("div"),
           Typ    => EW_Int_Type);
      M_Int_Div.Rem_Id :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("rem"),
           Typ    => EW_Int_Type);
      M_Int_Div.Mod_Id :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("mod"),
           Typ    => EW_Int_Type);
      M_Int_Div.Math_Mod :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("math_mod"),
           Typ    => EW_Int_Type);
   end Init_Int_Div_Module;

   ---------------------------
   -- Init_Int_Gcd_Module --
   ---------------------------

   procedure Init_Int_Gcd_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Int_Gcd");
   begin
      M_Int_Gcd.Module := M;
      M_Int_Gcd.Gcd :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("gcd"),
           Typ    => EW_Int_Type);
   end Init_Int_Gcd_Module;

   ----------------------------
   -- Init_Int_Minmax_Module --
   ----------------------------

   procedure Init_Int_Minmax_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Int_Minmax");

   begin
      M_Int_Minmax.Module := M;
      M_Int_Minmax.Max :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("int_max"),
           Typ    => EW_Int_Type);
      M_Int_Minmax.Min :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("int_min"),
           Typ    => EW_Int_Type);
   end Init_Int_Minmax_Module;

   ---------------------------
   -- Init_Int_Power_Module --
   ---------------------------

   procedure Init_Int_Power_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Int_Power");
   begin
      M_Int_Power.Module := M;
      M_Int_Power.Power :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("power"),
           Typ    => EW_Int_Type);
   end Init_Int_Power_Module;

   ---------------------------
   -- Init_Int_Shift_Module --
   ---------------------------

   procedure Init_Int_Shift_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Int_Shift");
   begin
      M_Int_Shift.Module := M;
      M_Int_Shift.Shift_Left :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("shift_left"),
           Typ    => EW_Int_Type);
      M_Int_Shift.Shift_Right :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("shift_right"),
           Typ    => EW_Int_Type);
      M_Int_Shift.Shift_Right_Arithmetic :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("shift_right_arithmetic"),
           Typ    => EW_Int_Type);
      M_Int_Shift.Rotate_Left :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("rotate_left"),
           Typ    => EW_Int_Type);
      M_Int_Shift.Rotate_Right :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("rotate_right"),
           Typ    => EW_Int_Type);
   end Init_Int_Shift_Module;

   -------------------------
   -- Init_Integer_Module --
   -------------------------

   procedure Init_Integer_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Integer");
   begin
      M_Integer.Module := M;
      M_Integer.Bool_Eq :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_eq"),
           Typ    => EW_Bool_Type);
      M_Integer.Bool_Ne :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_ne"),
           Typ    => EW_Bool_Type);
      M_Integer.Bool_Le :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_le"),
           Typ    => EW_Bool_Type);
      M_Integer.Bool_Lt :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_lt"),
           Typ    => EW_Bool_Type);
      M_Integer.Bool_Ge :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_ge"),
           Typ    => EW_Bool_Type);
      M_Integer.Bool_Gt :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_gt"),
           Typ    => EW_Bool_Type);
      M_Integer.Length :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("length"),
           Typ    => EW_Int_Type);
   end Init_Integer_Module;

   -----------------
   -- Init_Labels --
   -----------------

   procedure Init_Labels is
   begin
      Model_Trace := NID (Model_Trace_Label);
      Model_Projected := NID (Model_Proj_Label);
      VC_Annotation := NID (VC_Annotation_Label);
      Model_VC_Post := NID (Model_VC_Post_Label);
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
        New_Type
          (Type_Kind  => EW_Abstract,
           Name       => New_Name (Symb => NID ("__image"), Module => M),
           Is_Mutable => False);

      M_Main.Type_Of_Heap :=
        New_Type
          (Type_Kind  => EW_Abstract,
           Name       =>
             New_Name (Symb => NID ("__type_of_heap"), Module => M),
           Is_Mutable => False);
      M_Main.Fixed_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("__fixed"), Module => M),
           Is_Mutable => False);
      M_Main.Private_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("__private"), Module => M),
           Is_Mutable => False);
      M_Main.Private_Bool_Eq :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("private__bool_eq"),
           Typ    => EW_Bool_Type);

      M_Main.Return_Exc := New_Name (Symb => NID ("Return__exc"));

      M_Main.Ada_Exc := New_Name (Symb => NID ("Ada__exc"));

      M_Main.Program_Exit_Exc := New_Name (Symb => NID ("Program_exit__exc"));

      M_Main.Spark_CE_Branch :=
        New_Identifier
          (Domain => EW_Term,
           Module => M,
           Symb   => NID ("spark__branch"),
           Typ    => EW_Bool_Type);

      EW_Private_Type := M_Main.Private_Type;
   end Init_Main_Module;

   --------------------------
   -- Init_Real_Abs_Module --
   --------------------------

   procedure Init_Real_Abs_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Real_Abs");
   begin
      M_Real_Abs.Module := M;
      M_Real_Abs.Abs_Id :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("abs"),
           Typ    => EW_Real_Type);
   end Init_Real_Abs_Module;

   -------------------------------
   -- Init_Real_From_Int_Module --
   -------------------------------

   procedure Init_Real_From_Int_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Real_FromInt");

   begin
      M_Real_From_Int.Module := M;
      M_Real_From_Int.From_Int :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("from_int"),
           Typ    => EW_Real_Type);
   end Init_Real_From_Int_Module;

   -----------------------------
   -- Init_Real_Minmax_Module --
   -----------------------------

   procedure Init_Real_Minmax_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Real_Minmax");

   begin
      M_Real_Minmax.Module := M;
      M_Real_Minmax.Max :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("max"),
           Typ    => EW_Real_Type);
      M_Real_Minmax.Min :=
        New_Identifier
          (Module => M,
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
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_eq"),
           Typ    => EW_Bool_Type);
      M_Real.Bool_Ne :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_ne"),
           Typ    => EW_Bool_Type);
      M_Real.Bool_Le :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_le"),
           Typ    => EW_Bool_Type);
      M_Real.Bool_Lt :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_lt"),
           Typ    => EW_Bool_Type);
      M_Real.Bool_Ge :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_ge"),
           Typ    => EW_Bool_Type);
      M_Real.Bool_Gt :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("bool_gt"),
           Typ    => EW_Bool_Type);
      M_Real.Div :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("div"),
           Typ    => EW_Real_Type);
   end Init_Real_Module;

   ----------------------------
   -- Init_Real_Power_Module --
   ----------------------------

   procedure Init_Real_Power_Module is
      M : constant W_Module_Id :=
        New_Module (File => Gnatprove_Standard_File, Name => "Real_Power");
   begin
      M_Real_Power.Module := M;
      M_Real_Power.Power :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("power"),
           Typ    => EW_Real_Type);
   end Init_Real_Power_Module;

   -----------------------------------
   -- Init_Subprogram_Access_Module --
   -----------------------------------

   procedure Init_Subprogram_Access_Module is
      M : constant W_Module_Id :=
        New_Module
          (File => Gnatprove_Standard_File, Name => "Subprogram_Pointer_Rep");
   begin
      M_Subprogram_Access.Module := M;
      M_Subprogram_Access.Subprogram_Type :=
        New_Type
          (Type_Kind  => EW_Builtin,
           Name       => New_Name (Symb => NID ("__subprogram"), Module => M),
           Is_Mutable => False);
      M_Subprogram_Access.Dummy :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("__dummy_subprogram"),
           Typ    => M_Subprogram_Access.Subprogram_Type);
      M_Subprogram_Access.Access_Rep_Type :=
        New_Name (Symb => NID ("__rep"), Module => M);
      M_Subprogram_Access.Rec_Is_Null :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("__is_null_pointer"),
           Typ    => EW_Bool_Type);
      M_Subprogram_Access.Rec_Value :=
        New_Identifier
          (Module => M,
           Domain => EW_Term,
           Symb   => NID ("__pointer_value"),
           Typ    => M_Subprogram_Access.Subprogram_Type);
      M_Subprogram_Access.Rec_Value_Prog :=
        New_Identifier
          (Module => M,
           Domain => EW_Prog,
           Symb   => NID ("__pointer_value_"),
           Typ    => M_Subprogram_Access.Subprogram_Type);
   end Init_Subprogram_Access_Module;

   -------------------------
   -- Insert_Extra_Module --
   -------------------------

   procedure Insert_Extra_Module
     (N : Node_Id; M : W_Module_Id; Kind : Module_Kind := Regular)
   is
      Position : Ada_Node_To_Module.Cursor;
      Inserted : Boolean;
   begin
      Entity_Modules.Insert
        (N, Module_Kind_To_Module.Empty_Map, Position, Inserted);
      Entity_Modules (Position).Insert (Kind, M);
   end Insert_Extra_Module;

   ------------------------
   -- Insert_Why_Symbols --
   ------------------------

   procedure Insert_Why_Symbols (E : Entity_Id) is

      procedure Insert_Symbol
        (E            : Entity_Id;
         W            : Why_Name_Enum;
         I            : W_Identifier_Id;
         Relaxed_Init : Boolean := False);
      --  For the key (E, W), add the symbol I to the symbol map
      --  @param E the entity part of the key
      --  @param W the symbol part of the key
      --  @param I the identifier to be added
      --  @param Relaxed_Init if True, insert the symbol in the map for
      --     initialization wrapper symbols.

      procedure Insert_Type_Symbols (E : Entity_Id)
      with Pre => Is_Type (E);
      --  Add the symbols for type entity E
      --  @param E a type entity

      procedure Insert_Shared_Type_Symbols
        (E : Entity_Id; Relaxed_Init : Boolean := False)
      with Pre => Is_Type (E);
      --  Add the symbols that are shared between the regular theory for type
      --  entity E and its initialization wrapper theory.
      --  @param E a type entity
      --  @param Relaxed_Init if True, insert the initialization wrapper
      --     symbols.

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

      procedure Insert_Symbol
        (E            : Entity_Id;
         W            : Why_Name_Enum;
         I            : W_Identifier_Id;
         Relaxed_Init : Boolean := False) is
      begin
         if Relaxed_Init then
            Why_Relaxed_Symb_Map.Insert (Why_Symb'(E, W), I);
         else
            Why_Symb_Map.Insert (Why_Symb'(E, W), I);
         end if;
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
           (E,
            WNE_Attr_First_Bit,
            New_Identifier
              (Symb   => NID (Name & "__first__bit"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));
         Insert_Symbol
           (E,
            WNE_Attr_Last_Bit,
            New_Identifier
              (Symb   => NID (Name & "__last__bit"),
               Module => M,
               Domain => EW_Term,
               Typ    => EW_Int_Type));
         Insert_Symbol
           (E,
            WNE_Attr_Position,
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
         M_Prog : constant W_Module_Id := E_Module (E, Program_Function_Decl);
         Name   : constant String := Short_Name (E);

      begin
         if Ekind (E) = E_Function then
            if not Has_Pragma_Volatile_Function (E)
              and then not Is_Function_With_Side_Effects (E)
            then
               Insert_Symbol
                 (E,
                  WNE_Func_Guard,
                  New_Identifier
                    (Symb   => NID (Name & "__" & Function_Guard),
                     Module => E_Module (E, Logic_Function_Decl),
                     Domain => EW_Pred,
                     Typ    => EW_Unit_Type));

               if Is_Dispatching_Operation (E)
                 and then not Is_Hidden_Dispatching_Operation (E)
               then
                  Insert_Symbol
                    (E,
                     WNE_Dispatch_Func_Guard,
                     New_Identifier
                       (Symb   => NID (Name & "__" & Function_Guard),
                        Module => E_Module (E, Dispatch),
                        Domain => EW_Pred,
                        Typ    => EW_Unit_Type));
               end if;
            end if;
         elsif Is_Dispatching_Operation (E)
           and then not Is_Hidden_Dispatching_Operation (E)
         then
            Insert_Symbol
              (E,
               WNE_Specific_Post,
               New_Identifier
                 (Symb   => NID (Name & "__" & Specific_Post),
                  Module => E_Module (E, Dispatch),
                  Domain => EW_Pred,
                  Typ    => EW_Unit_Type));
         end if;

         if Present (Get_Pragma (E, Pragma_Subprogram_Variant)) then
            Insert_Symbol
              (E,
               WNE_Check_Subprogram_Variants,
               New_Identifier
                 (Symb   => NID (Name & "__check_subprogram_variants"),
                  Module => M_Prog,
                  Domain => EW_Prog,
                  Typ    => EW_Unit_Type));
         end if;

         if Get_Termination_Condition (E).Kind = Dynamic then
            Insert_Symbol
              (E,
               WNE_Check_Termination_Condition,
               New_Identifier
                 (Symb   => NID (Name & "__check_termination_condition"),
                  Module => M_Prog,
                  Domain => EW_Prog,
                  Typ    => EW_Unit_Type));
         end if;
      end Insert_Subprogram_Symbols;

      --------------------------------
      -- Insert_Shared_Type_Symbols --
      --------------------------------

      procedure Insert_Shared_Type_Symbols
        (E : Entity_Id; Relaxed_Init : Boolean := False)
      is
         M  : constant W_Module_Id :=
           E_Module (E, (if Relaxed_Init then Init_Wrapper else Regular));
         Ty : constant W_Type_Id := EW_Abstract (E, Relaxed_Init);

      begin
         --  In wrapper modules for initialization, Dummy is not introduced for
         --  composite types.

         if not Relaxed_Init
           or else Is_Scalar_Type (E)
           or else Is_Simple_Private_Type (E)
         then
            Insert_Symbol
              (E,
               WNE_Dummy,
               New_Identifier
                 (Symb   => NID ("dummy"),
                  Module => M,
                  Domain => EW_Term,
                  Typ    => Ty),
               Relaxed_Init);
         end if;

         --  The equality symbol is only needed for pointers in wrapper
         --  modules, as for other types, checking the equality requires the
         --  operands to be initialized.

         if not Relaxed_Init
           or else
             (Has_Access_Type (E) and then not Is_Access_Subprogram_Type (E))
         then
            Insert_Symbol
              (E,
               WNE_Bool_Eq,
               New_Identifier
                 (Symb   => NID ("bool_eq"),
                  Module => M,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type),
               Relaxed_Init);
         end if;

         --  Symbols for record types

         if Is_Record_Type_In_Why (E) then
            declare
               Root    : constant Entity_Id := Root_Retysp (E);
               Root_Ty : constant W_Type_Id :=
                 New_Named_Type (To_Why_Type (Root, Relaxed_Init));
            begin
               Insert_Symbol
                 (E,
                  WNE_To_Base,
                  New_Identifier
                    (Symb   => NID ("to_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Root_Ty),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Of_Base,
                  New_Identifier
                    (Symb   => NID ("of_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Rec_Split_Discrs,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Split_Discrs)),
                     Module => M,
                     Domain => EW_Term),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Rec_Split_Fields,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Rec_Split_Fields)),
                     Module => M,
                     Domain => EW_Term),
                  Relaxed_Init);

               --  For types which have their own private part, introduce a
               --  symbol for the type of the component modelling this part.

               if Has_Private_Part (E) and then not Is_Simple_Private_Type (E)
               then
                  declare
                     Main_Type : constant W_Identifier_Id :=
                       New_Identifier
                         (Symb   => NID ("__main_type"),
                          Module => M,
                          Domain => EW_Term);
                  begin
                     Insert_Symbol
                       (E, WNE_Private_Type, Main_Type, Relaxed_Init);
                     Insert_Symbol
                       (E,
                        WNE_Private_Dummy,
                        New_Identifier
                          (Symb   => NID ("__main_dummy"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    =>
                             New_Named_Type
                               (Name         => Get_Name (Main_Type),
                                Relaxed_Init => Relaxed_Init)),
                        Relaxed_Init);
                  end;
               end if;
            end;

         --  Symbols for array types

         elsif Has_Array_Type (E) then
            declare
               Ar_Dim : constant Positive := Positive (Number_Dimensions (E));
            begin
               Insert_Symbol
                 (E,
                  WNE_To_Array,
                  New_Identifier
                    (Symb   => NID ("to_array"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Get_Array_Theory (E, Relaxed_Init).Ty),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Of_Array,
                  New_Identifier
                    (Symb   => NID ("of_array"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Array_Elts,
                  New_Identifier
                    (Symb   => NID ("elts"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Get_Array_Theory (E, Relaxed_Init).Ty),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Array_Well_Formed,
                  New_Identifier
                    (Symb   => NID ("well_formed"),
                     Module => M,
                     Domain => EW_Pred),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Array_Logic_Eq,
                  New_Identifier
                    (Symb => NID ("logic_eq"), Module => M, Domain => EW_Pred),
                  Relaxed_Init);

               for Dim in 1 .. Ar_Dim loop
                  declare
                     First_Str  : constant String :=
                       (if Dim = 1
                        then "first"
                        else "first_" & Image (Dim, 1));
                     Last_Str   : constant String :=
                       (if Dim = 1 then "last" else "last_" & Image (Dim, 1));
                     Length_Str : constant String :=
                       (if Dim = 1
                        then "length"
                        else "length_" & Image (Dim, 1));
                  begin
                     Insert_Symbol
                       (E,
                        WNE_Attr_First (Dim),
                        New_Identifier
                          (Symb   => NID (First_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type),
                        Relaxed_Init);
                     Insert_Symbol
                       (E,
                        WNE_Attr_Last (Dim),
                        New_Identifier
                          (Symb   => NID (Last_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type),
                        Relaxed_Init);
                     Insert_Symbol
                       (E,
                        WNE_Attr_Length (Dim),
                        New_Identifier
                          (Symb   => NID (Length_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type),
                        Relaxed_Init);
                  end;
               end loop;
            end;
         elsif Has_Access_Type (E) and then not Is_Access_Subprogram_Type (E)
         then
            declare
               Is_Incompl     : constant Boolean :=
                 Designates_Incomplete_Type (Repr_Pointer_Type (E));
               Root           : constant Entity_Id := Root_Pointer_Type (E);
               Root_Ty        : constant W_Type_Id :=
                 EW_Abstract (Root, Relaxed_Init);
               Full_Name_Node : constant String := Full_Name (Root);
               M_C            : constant W_Module_Id :=
                 (if not Is_Incompl
                  then M
                  else
                    E_Module
                      (Repr_Pointer_Type (E),
                       (if Relaxed_Init
                        then Init_Wrapper_Completion
                        else Type_Completion)));
               Des_Ty         : constant Entity_Id :=
                 Directly_Designated_Type (Retysp (E));
               W_Des_Ty       : constant W_Type_Id :=
                 EW_Abstract
                   (Des_Ty,
                    Relaxed_Init =>
                      (if Relaxed_Init
                       then Has_Init_Wrapper (Des_Ty)
                       else Has_Relaxed_Init (Des_Ty)));

            begin
               Insert_Symbol
                 (E,
                  WNE_Is_Null_Pointer,
                  New_Identifier
                    (Symb   =>
                       NID
                         (To_String (WNE_Rec_Comp_Prefix)
                          & Full_Name_Node
                          & "__is_null_pointer"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type),
                  Relaxed_Init);

               Insert_Symbol
                 (E,
                  WNE_Pointer_Value,
                  New_Identifier
                    (Symb   =>
                       NID
                         (To_String (WNE_Rec_Comp_Prefix)
                          & Full_Name_Node
                          & "__pointer_value"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => W_Des_Ty),
                  Relaxed_Init);

               Insert_Symbol
                 (E,
                  WNE_To_Base,
                  New_Identifier
                    (Symb   => NID ("to_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Root_Ty),
                  Relaxed_Init);
               Insert_Symbol
                 (E,
                  WNE_Of_Base,
                  New_Identifier
                    (Symb   => NID ("of_base"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Ty),
                  Relaxed_Init);

               Insert_Symbol
                 (E,
                  WNE_Assign_Null_Check,
                  New_Identifier
                    (Symb   => NID ("assign_null_check"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Ty),
                  Relaxed_Init);

               if Root /= Repr_Pointer_Type (E) then
                  Insert_Symbol
                    (E,
                     WNE_Range_Check_Fun,
                     New_Identifier
                       (Symb   => NID ("range_check_"),
                        Module => M_C,
                        Domain => EW_Term,
                        Typ    => Root_Ty),
                     Relaxed_Init);
                  Insert_Symbol
                    (E,
                     WNE_Range_Pred,
                     New_Identifier
                       (Module => M_C,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type),
                     Relaxed_Init);
               end if;

               Insert_Symbol
                 (E,
                  WNE_Dynamic_Property,
                  New_Identifier
                    (Symb   => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type),
                  Relaxed_Init);

               if Is_Incompl then
                  Insert_Symbol
                    (E,
                     WNE_Private_Type,
                     New_Identifier
                       (Symb   => NID ("__main_type"),
                        Module => M,
                        Domain => EW_Term),
                     Relaxed_Init);
                  Insert_Symbol
                    (E,
                     WNE_Dummy_Abstr,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Dummy_Abstr)),
                        Module => M,
                        Domain => EW_Term,
                        Typ    =>
                          New_Named_Type
                            (Name         =>
                               New_Name
                                 (Symb => NID ("__main_type"), Module => M),
                             Relaxed_Init => Relaxed_Init)),
                     Relaxed_Init);
                  Insert_Symbol
                    (E,
                     WNE_Pointer_Value_Abstr,
                     New_Identifier
                       (Symb   =>
                          NID
                            (To_String (WNE_Rec_Comp_Prefix)
                             & Full_Name_Node
                             & "__pointer_value_abstr"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    =>
                          New_Named_Type
                            (Name         =>
                               New_Name
                                 (Symb => NID ("__main_type"), Module => M),
                             Relaxed_Init => Relaxed_Init)),
                     Relaxed_Init);
                  Insert_Symbol
                    (E,
                     WNE_Open,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Open)),
                        Module => M_C,
                        Domain => EW_Term,
                        Typ    => W_Des_Ty),
                     Relaxed_Init);
                  Insert_Symbol
                    (E,
                     WNE_Close,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Close)),
                        Module => M_C,
                        Domain => EW_Term,
                        Typ    =>
                          New_Named_Type
                            (Name         =>
                               New_Name
                                 (Symb => NID ("__main_type"), Module => M),
                             Relaxed_Init => Relaxed_Init)),
                     Relaxed_Init);
                  Insert_Symbol
                    (E,
                     WNE_Static_Constraint,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Static_Constraint)),
                        Module => M_C,
                        Domain => EW_Pred),
                     Relaxed_Init);
               end if;
            end;
         end if;
      end Insert_Shared_Type_Symbols;

      -------------------------
      -- Insert_Type_Symbols --
      -------------------------

      procedure Insert_Type_Symbols (E : Entity_Id) is
         M    : constant W_Module_Id := E_Module (E);
         AM   : constant W_Module_Id := E_Module (E, Axiom);
         Name : constant String := Short_Name (E);
         Ty   : constant W_Type_Id := EW_Abstract (E);

      begin
         --  Insert symbols which are defined both in the normal and in the
         --  Init_Wrapper module of E.

         Insert_Shared_Type_Symbols (E);

         --  Insert symbols for the initialization wrapper if any

         if Has_Init_Wrapper (E) then
            declare
               WM : constant W_Module_Id := E_Module (E, Init_Wrapper);

            begin
               Insert_Shared_Type_Symbols (E, Relaxed_Init => True);

               Insert_Symbol
                 (E,
                  WNE_Is_Initialized_Pred,
                  New_Identifier
                    (Symb   => NID ("__is_initialized"),
                     Module =>
                       (if Has_Predeclared_Init_Predicate (E) then WM else AM),
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));

               --  We need extra fields to create the wrapper type for scalars
               --  and simple private types.

               if Has_Scalar_Type (E) or else Is_Simple_Private_Type (E) then
                  Insert_Symbol
                    (E,
                     WNE_Init_Value,
                     New_Identifier
                       (Symb   => NID ("rec__value"),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => Ty));
                  Insert_Symbol
                    (E,
                     WNE_Attr_Init,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Attr_Init)),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));

               --  Records with mutable discriminants and access-to-objects
               --  also have a specific flag.

               elsif Has_Mutable_Discriminants (E)
                 or else
                   (Is_Access_Type (E)
                    and then not Is_Access_Subprogram_Type (E))
               then
                  Insert_Symbol
                    (E,
                     WNE_Attr_Init,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Attr_Init)),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => EW_Bool_Type));
               end if;

               --  We do not need conversion functions to and from the wrapper
               --  types for arrays. Indeed conversion goes through the base
               --  array type, so conversion functions are rather stored with
               --  other array conversion theories.

               if not Is_Array_Type (E) then
                  Insert_Symbol
                    (E,
                     WNE_To_Wrapper,
                     New_Identifier
                       (Symb   => NID ("to_wrapper"),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => EW_Init_Wrapper (Ty)));
                  Insert_Symbol
                    (E,
                     WNE_Of_Wrapper,
                     New_Identifier
                       (Symb   => NID ("of_wrapper"),
                        Module => WM,
                        Domain => EW_Term,
                        Typ    => Ty));
               end if;
            end;
         end if;

         if not Use_Predefined_Equality_For_Type (E) then
            Insert_Symbol
              (E,
               WNE_User_Eq,
               New_Identifier
                 (Symb   => NID ("user_eq"),
                  Module => E_Module (E, User_Equality),
                  Domain => EW_Term,
                  Typ    => EW_Int_Type));
         end if;

         --  Add symbol for the predicate used to assume the dynamic invariant
         --  of a type. This symbol is registered in the axiom module, so that
         --  the function can be directly defined there instead of being first
         --  declared in the entity module and then axiomatized in the axiom
         --  module (to have visibility over constants/functions in the
         --  definition).

         if not Is_Itype (E) then
            Insert_Symbol
              (E,
               WNE_Dynamic_Invariant,
               New_Identifier
                 (Symb   => NID ("dynamic_invariant"),
                  Module => AM,
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));

            if Has_Init_Wrapper (E) then
               Insert_Symbol
                 (E,
                  WNE_Dynamic_Invariant,
                  New_Identifier
                    (Symb   => NID ("dynamic_invariant_r"),
                     Module => AM,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type),
                  Relaxed_Init => True);
            end if;
         end if;

         --  Add symbol for the function checking that the invariant of a type
         --  holds. This symbol is registered in the axiom module, so that
         --  the function can be directly defined there instead of being first
         --  declared in the entity module and then axiomatized in the axiom
         --  module (to have visibility over constants/functions in the
         --  definition).

         if Has_Invariants_In_SPARK (E) then
            Insert_Symbol
              (E,
               WNE_Type_Invariant,
               New_Identifier
                 (Symb   => NID ("type_invariant"),
                  Module => E_Module (E, Invariant),
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
              (E,
               WNE_Default_Init,
               New_Identifier
                 (Symb   => NID ("default_initial_assumption"),
                  Module => E_Module (E, Default_Initialialization),
                  Domain => EW_Term,
                  Typ    => EW_Bool_Type));
         end if;

         --  If E needs reclamation, insert symbols for the
         --  is_moved_or_reclaimed property and moved_tree function.

         if Contains_Allocated_Parts (E) then
            Insert_Symbol
              (E,
               WNE_Is_Moved_Or_Reclaimed,
               New_Identifier
                 (Symb   => NID (To_String (WNE_Is_Moved_Or_Reclaimed)),
                  Module => E_Module (E, Move_Tree),
                  Domain => EW_Pred));
            Insert_Symbol
              (E,
               WNE_Moved_Tree,
               New_Identifier
                 (Symb   => NID (To_String (WNE_Moved_Tree)),
                  Module => E_Module (E, Move_Tree),
                  Domain => EW_Prog,
                  Typ    => Get_Move_Tree_Type (E)));

            --  Symbols to construct the move tree

            if Is_Array_Type (E) then
               Insert_Symbol
                 (E,
                  WNE_Move_Tree_Array_Get,
                  New_Identifier
                    (Domain => EW_Term,
                     Symb   => NID (To_String (WNE_Move_Tree_Array_Get)),
                     Typ    => Get_Move_Tree_Type (Component_Type (E)),
                     Module => E_Module (E, Move_Tree)));
               Insert_Symbol
                 (E,
                  WNE_Move_Tree_Array_Set,
                  New_Identifier
                    (Domain => EW_Prog,
                     Symb   => NID (To_String (WNE_Move_Tree_Array_Set)),
                     Typ    => Get_Move_Tree_Type (E),
                     Module => E_Module (E, Move_Tree)));

            elsif Is_Access_Type (E)
              and then not Is_General_Access_Type (E)
              and then not Is_Anonymous_Access_Type (E)
            then
               Insert_Symbol
                 (E,
                  WNE_Move_Tree_Ptr_Is_Moved,
                  New_Identifier
                    (Domain => EW_Term,
                     Symb   => NID (To_String (WNE_Move_Tree_Ptr_Is_Moved)),
                     Typ    => EW_Bool_Type,
                     Module => E_Module (E, Move_Tree)));

               if Contains_Allocated_Parts (Directly_Designated_Type (E)) then
                  declare
                     Des_Ty     : constant Entity_Id :=
                       Retysp (Directly_Designated_Type (E));
                     Des_Module : constant W_Module_Id :=
                       (if Designates_Incomplete_Type (E)
                        then E_Module (Des_Ty, Incomp_Move_Tree)
                        else E_Module (Des_Ty, Move_Tree));
                     --  For incomplete designated types, use early declaration

                  begin
                     Insert_Symbol
                       (E,
                        WNE_Move_Tree_Ptr_Value,
                        New_Identifier
                          (Domain => EW_Term,
                           Symb   => NID (To_String (WNE_Move_Tree_Ptr_Value)),
                           Typ    =>
                             New_Named_Type
                               (Name =>
                                  New_Name
                                    (Symb   => NID (To_String (WNE_Move_Tree)),
                                     Module => Des_Module)),
                           Module => E_Module (E, Move_Tree)));
                  end;
               end if;
            end if;

            --  Open and close functions for move trees of incomplete types

            if Has_Incomplete_Access (E) then
               Insert_Symbol
                 (E,
                  WNE_Move_Tree_Open,
                  New_Identifier
                    (Domain => EW_Term,
                     Symb   => NID (To_String (WNE_Move_Tree_Open)),
                     Typ    => Get_Move_Tree_Type (E),
                     Module => E_Module (E, Move_Tree)));
               Insert_Symbol
                 (E,
                  WNE_Move_Tree_Close,
                  New_Identifier
                    (Domain => EW_Prog,
                     Symb   => NID (To_String (WNE_Move_Tree_Close)),
                     Typ    =>
                       New_Named_Type
                         (Name =>
                            New_Name
                              (Symb   => NID (To_String (WNE_Move_Tree)),
                               Module => E_Module (E, Incomp_Move_Tree))),
                     Module => E_Module (E, Move_Tree)));
            end if;
         end if;

         --  Symbols for validity trees and wrapper for function result

         if Type_Might_Be_Invalid (E) then

            --  For non-scalar types, introduce symbols for validity trees.
            --  They are shared in the module of the root retysp.

            if not Has_Scalar_Type (E) then
               declare
                  V_M     : constant W_Module_Id :=
                    E_Module (Base_Retysp (E), Validity_Tree);
                  Tree_Ty : constant W_Type_Id := Get_Validity_Tree_Type (E);
               begin
                  Insert_Symbol
                    (E,
                     WNE_Is_Valid,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Is_Valid)),
                        Module => V_M,
                        Domain => EW_Pred));
                  Insert_Symbol
                    (E,
                     WNE_Valid_Value,
                     New_Identifier
                       (Symb   => NID (To_String (WNE_Valid_Value)),
                        Module => V_M,
                        Domain => EW_Pterm,
                        Typ    => Tree_Ty));

                  if Is_Array_Type (E) then
                     Insert_Symbol
                       (E,
                        WNE_Validity_Tree_Get,
                        New_Identifier
                          (Domain => EW_Term,
                           Symb   => NID (To_String (WNE_Validity_Tree_Get)),
                           Typ    =>
                             Get_Validity_Tree_Type (Component_Type (E)),
                           Module => V_M));
                     Insert_Symbol
                       (E,
                        WNE_Validity_Tree_Set,
                        New_Identifier
                          (Domain => EW_Prog,
                           Symb   => NID (To_String (WNE_Validity_Tree_Set)),
                           Typ    => Tree_Ty,
                           Module => V_M));
                     Insert_Symbol
                       (E,
                        WNE_Validity_Tree_Slide,
                        New_Identifier
                          (Domain => EW_Prog,
                           Symb   => NID (To_String (WNE_Validity_Tree_Slide)),
                           Typ    => Tree_Ty,
                           Module => V_M));
                  end if;
               end;
            end if;

            --  Generate the symbols for function results

            declare
               VM : constant W_Module_Id :=
                 E_Module (Retysp (E), Validity_Wrapper);
            begin
               Insert_Symbol
                 (E,
                  WNE_Valid_Wrapper,
                  New_Identifier
                    (Symb   => NID (To_String (WNE_Valid_Wrapper)),
                     Module => VM,
                     Domain => EW_Term));
               Insert_Symbol
                 (E,
                  WNE_Valid_Wrapper_Flag,
                  New_Identifier
                    (Symb   => NID ("__valid_wrapper_flag"),
                     Module => VM,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));
               Insert_Symbol
                 (E,
                  WNE_Valid_Wrapper_Result,
                  New_Identifier
                    (Symb   => NID ("__valid_wrapper_result"),
                     Module => VM,
                     Domain => EW_Term,
                     Typ    => Type_Of_Node (E)));
            end;
         end if;

         --  Symbols for scalar types

         if Is_Scalar_Type (E) then
            declare
               Base : constant W_Type_Id := Get_EW_Term_Type (E);
            begin
               Insert_Symbol
                 (E,
                  WNE_Attr_Image,
                  New_Identifier
                    (Symb   => NID ("attr__ATTRIBUTE_IMAGE"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => M_Main.String_Image_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Value,
                  New_Identifier
                    (Symb   => NID ("attr__ATTRIBUTE_VALUE"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E,
                  WNE_Check_Not_First,
                  New_Identifier
                    (Symb   => NID ("check_not_first"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E,
                  WNE_Check_Not_Last,
                  New_Identifier
                    (Symb   => NID ("check_not_last"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E,
                  WNE_Range_Check_Fun,
                  New_Identifier
                    (Symb   => NID ("range_check_"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E,
                  WNE_Dynamic_Property,
                  New_Identifier
                    (Symb   => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));

               --  For types translated to range types in Why, declare
               --  predifined projection function.

               if Is_Range_Type_In_Why (E) then
                  Insert_Symbol
                    (E,
                     WNE_Int_Proj,
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
                     then E_Module (E, Type_Representative)
                     else M);

               begin
                  Insert_Symbol
                    (E,
                     WNE_To_Rep,
                     New_Identifier
                       (Module => RM,
                        Domain => EW_Term,
                        Symb   => NID ("to_rep"),
                        Typ    => Base));

                  Insert_Symbol
                    (E,
                     WNE_Of_Rep,
                     New_Identifier
                       (Module => RM,
                        Domain => EW_Term,
                        Symb   => NID ("of_rep"),
                        Typ    => Ty));
               end;

               Insert_Symbol
                 (E,
                  WNE_Attr_First,
                  New_Identifier
                    (Symb   => NID ("first"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));
               Insert_Symbol
                 (E,
                  WNE_Attr_Last,
                  New_Identifier
                    (Symb   => NID ("last"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => Base));

               --  Symbols for static scalar types

               if not Type_Is_Modeled_As_Base (E) then
                  Insert_Symbol
                    (E,
                     WNE_Range_Pred,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type));
               end if;

               --  Symbols for modular types

               if Has_Modular_Operations (E) then
                  declare
                     RM : constant W_Module_Id :=
                       E_Module (E, Type_Representative);
                  begin
                     Insert_Symbol
                       (E,
                        WNE_Attr_Modulus,
                        New_Identifier
                          (Symb   => NID ("attr__ATTRIBUTE_MODULUS"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => Base));

                     if not Has_No_Bitwise_Operations_Annotation (E) then
                        Insert_Symbol
                          (E,
                           WNE_To_Int,
                           New_Identifier
                             (Symb   => NID ("to_int"),
                              Module => RM,
                              Domain => EW_Term,
                              Typ    => EW_Int_Type));
                        Insert_Symbol
                          (E,
                           WNE_Of_BitVector,
                           New_Identifier
                             (Symb   => NID ("of_int"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    => Base));
                        Insert_Symbol
                          (E,
                           WNE_Dynamic_Property_BV_Int,
                           New_Identifier
                             (Symb   => NID ("dynamic_property_int"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    => EW_Bool_Type));
                        Insert_Symbol
                          (E,
                           WNE_Range_Check_Fun_BV_Int,
                           New_Identifier
                             (Symb   => NID ("range_check_int_"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    => EW_Int_Type));
                     end if;
                  end;
               end if;

               --  Symbols for modular static types

               if Is_Bitvector_Type_In_Why (E)
                 and then not Type_Is_Modeled_As_Base (E)
               then
                  Insert_Symbol
                    (E,
                     WNE_Range_Pred_BV_Int,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range_int"),
                        Typ    => EW_Bool_Type));
               end if;

               --  Symbols for fixed point types

               if Is_Fixed_Point_Type (E) then
                  Insert_Symbol
                    (E,
                     WNE_Small_Num,
                     New_Identifier
                       (Symb   => NID ("num_small"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Base));
                  Insert_Symbol
                    (E,
                     WNE_Small_Den,
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
                    (E,
                     WNE_Pos_To_Rep,
                     New_Identifier
                       (Symb   => NID ("pos_to_rep"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E,
                     WNE_Rep_To_Pos,
                     New_Identifier
                       (Symb   => NID ("rep_to_pos"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
               end if;
            end;

         --  Symbols for record types

         elsif Is_Record_Type_In_Why (E) then
            declare
               Root    : constant Entity_Id := Root_Retysp (E);
               Root_Ty : constant W_Type_Id :=
                 New_Named_Type (To_Why_Type (Root));
            begin
               Insert_Symbol
                 (E,
                  WNE_Attr_Alignment,
                  New_Identifier
                    (Symb   => NID ("alignment"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Value_Size,
                  New_Identifier
                    (Symb   => NID ("value__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Object_Size,
                  New_Identifier
                    (Symb   => NID ("object__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Size_Of_Object,
                  New_Identifier
                    (Symb   => NID ("size__of__object"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));

               if Root = E
                 and then Has_Discriminants (E)
                 and then not Is_Constrained (E)
               then
                  Insert_Symbol
                    (E,
                     WNE_Range_Check_Fun,
                     New_Identifier
                       (Symb   => NID ("range_check_"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => Root_Ty));
                  Insert_Symbol
                    (E,
                     WNE_Range_Pred,
                     New_Identifier
                       (Module => M,
                        Domain => EW_Term,
                        Symb   => NID ("in_range"),
                        Typ    => EW_Bool_Type));
               end if;

               --  For types which have their own private part, introduce a
               --  symbol for the equality on the type of the component
               --  modelling this part.

               if Has_Private_Part (E) and then not Is_Simple_Private_Type (E)
               then
                  declare
                     WM        : W_Module_Id;
                     Main_Type : constant W_Identifier_Id :=
                       New_Identifier
                         (Symb   => NID ("__main_type"),
                          Module => M,
                          Domain => EW_Term);
                  begin
                     Insert_Symbol
                       (E,
                        WNE_Private_Eq,
                        New_Identifier
                          (Symb   => NID ("__main_eq"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));

                     --  If the type needs a wrapper for relaxed
                     --  initialization, introduce names for the components of
                     --  this wrapper and for conversion functions.

                     if Has_Init_Wrapper (E) then
                        WM := E_Module (E, Init_Wrapper);
                        Insert_Symbol
                          (E,
                           WNE_Init_Value,
                           New_Identifier
                             (Symb   => NID ("rec__value"),
                              Module => WM,
                              Domain => EW_Term,
                              Typ    =>
                                New_Named_Type
                                  (Name => Get_Name (Main_Type))));
                        Insert_Symbol
                          (E,
                           WNE_Private_Attr_Init,
                           New_Identifier
                             (Symb   => NID ("__main_attr__init"),
                              Module => WM,
                              Domain => EW_Term,
                              Typ    => EW_Bool_Type));
                        Insert_Symbol
                          (E,
                           WNE_Private_To_Wrapper,
                           New_Identifier
                             (Symb   => NID ("__main_to_wrapper"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    =>
                                New_Named_Type
                                  (Name         =>
                                     New_Name
                                       (Symb   => NID ("__main_type"),
                                        Module => WM),
                                   Relaxed_Init => True)));
                        Insert_Symbol
                          (E,
                           WNE_Private_Of_Wrapper,
                           New_Identifier
                             (Symb   => NID ("__main_of_wrapper"),
                              Module => M,
                              Domain => EW_Term,
                              Typ    =>
                                New_Named_Type
                                  (Name => Get_Name (Main_Type))));
                     end if;
                  end;
               end if;

               if Is_Tagged_Type (E) then
                  if E = Root then
                     Insert_Symbol
                       (E,
                        WNE_Dispatch_Eq,
                        New_Identifier
                          (Symb   => NID ("__dispatch_eq"),
                           Module => E_Module (E, Dispatch_Equality),
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                  end if;
                  Insert_Symbol
                    (E,
                     WNE_Attr_Tag,
                     New_Identifier
                       (Symb   => NID ("attr__tag"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  Insert_Symbol
                    (E,
                     WNE_Tag,
                     New_Identifier
                       (Symb   => NID ("__tag"),
                        Module => M,
                        Domain => EW_Term,
                        Typ    => EW_Int_Type));
                  declare
                     Ext_Type : constant W_Identifier_Id :=
                       New_Identifier
                         (Symb   => NID ("__ext_type"),
                          Module => M,
                          Domain => EW_Term);
                  begin
                     Insert_Symbol (E, WNE_Extension_Type, Ext_Type);
                     Insert_Symbol
                       (E,
                        WNE_Rec_Extension,
                        New_Identifier
                          (Symb   => NID ("rec__ext__"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    =>
                             New_Named_Type (Name => Get_Name (Ext_Type))));
                     Insert_Symbol
                       (E,
                        WNE_Null_Extension,
                        New_Identifier
                          (Symb   => NID ("null__ext__"),
                           Module => M,
                           Domain => EW_Term,
                           Typ    =>
                             New_Named_Type (Name => Get_Name (Ext_Type))));
                  end;
               end if;

               if Has_Defaulted_Discriminants (E) then
                  Insert_Symbol
                    (E,
                     WNE_Attr_Constrained,
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
                 (E,
                  WNE_Attr_Alignment,
                  New_Identifier
                    (Symb   => NID ("alignment"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Value_Size,
                  New_Identifier
                    (Symb   => NID ("value__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Object_Size,
                  New_Identifier
                    (Symb   => NID ("object__size"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Attr_Size_Of_Object,
                  New_Identifier
                    (Symb   => NID ("size__of__object"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Int_Type));
               Insert_Symbol
                 (E,
                  WNE_Dynamic_Property,
                  New_Identifier
                    (Symb   => NID ("dynamic_property"),
                     Module => M,
                     Domain => EW_Term,
                     Typ    => EW_Bool_Type));

               if Ar_Dim = 1 and then Is_Discrete_Type (Component_Type (E))
               then
                  declare
                     RM : constant W_Module_Id :=
                       (if not Type_Is_Modeled_As_Base (E)
                        then E_Module (E, Type_Representative)
                        else M);
                  begin
                     Insert_Symbol
                       (E,
                        WNE_To_Rep,
                        New_Identifier
                          (Module => RM,
                           Domain => EW_Term,
                           Symb   => NID ("to_rep"),
                           Typ    => EW_Abstract (Component_Type (E))));
                  end;
               end if;

               for Dim in 1 .. Ar_Dim loop
                  declare
                     Int_Str        : constant String :=
                       (if Dim = 1
                        then "to_int"
                        else "to_int_" & Image (Dim, 1));
                     Base_Range_Str : constant String :=
                       (if Dim = 1
                        then "in_range_base"
                        else "in_range_base_" & Image (Dim, 1));
                     Index_Str      : constant String :=
                       (if Dim = 1
                        then "index_dynamic_property"
                        else "index_dynamic_property_" & Image (Dim, 1));
                  begin
                     Insert_Symbol
                       (E,
                        WNE_To_Int (Dim),
                        New_Identifier
                          (Symb   => NID (Int_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Int_Type));
                     Insert_Symbol
                       (E,
                        WNE_Array_Base_Range_Pred (Dim),
                        New_Identifier
                          (Symb   => NID (Base_Range_Str),
                           Module => M,
                           Domain => EW_Term,
                           Typ    => EW_Bool_Type));
                     Insert_Symbol
                       (E,
                        WNE_Index_Dynamic_Property (Dim),
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
              (E,
               WNE_Null_Pointer,
               New_Identifier
                 (Symb   => NID ("__null_pointer"),
                  Module => M,
                  Domain => EW_Term,
                  Typ    => Ty));
            Insert_Symbol
              (E,
               WNE_Range_Pred,
               New_Identifier
                 (Module => M,
                  Domain => EW_Pred,
                  Symb   => NID ("__in_range"),
                  Typ    => EW_Bool_Type));
            Insert_Symbol
              (E,
               WNE_Pointer_Call,
               New_Identifier
                 (Module => AM,
                  Domain => EW_Prog,
                  Symb   => NID ("__call_"),
                  Typ    =>
                    (if Is_Function_Type
                          (Directly_Designated_Type (Retysp (E)))
                     then
                       Type_Of_Node
                         (Etype (Directly_Designated_Type (Retysp (E))))
                     else EW_Unit_Type)));
            Insert_Symbol
              (E,
               WNE_Assign_Null_Check,
               New_Identifier
                 (Symb   => NID ("assign_null_check"),
                  Module => M,
                  Domain => EW_Term,
                  Typ    => Ty));

         --  Symbols for other access types

         elsif Has_Access_Type (E) then
            declare
               Is_Incompl : constant Boolean :=
                 Designates_Incomplete_Type (Repr_Pointer_Type (E));
               M_C        : constant W_Module_Id :=
                 (if Is_Incompl
                  then E_Module (Repr_Pointer_Type (E), Type_Completion)
                  else M);

            begin
               Insert_Symbol
                 (E,
                  WNE_Null_Pointer,
                  New_Identifier
                    (Symb   => NID ("__null_pointer"),
                     Module => M_C,
                     Domain => EW_Term,
                     Typ    => Ty));
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
      elsif T = EW_Float_80_Type then
         return M_Floats (Float80);
      else
         raise Program_Error;
      end if;
   end MF_Floats;

   --------------------------------
   -- Mutually_Recursive_Modules --
   --------------------------------

   function Mutually_Recursive_Modules (E : Entity_Id) return Why_Node_Sets.Set
   is

      function Remove_Expr_Fun_Body (F : Entity_Id) return Boolean
      is (Is_Expression_Function_Or_Completion (F)
          and then Entity_Body_Compatible_With_SPARK (F)
          and then No (Retrieve_Inline_Annotation (F))
          and then Is_Recursive (F)
          and then Has_Subprogram_Variant (F)
          and then
            not Is_Structural_Subprogram_Variant
                  (Get_Pragma (F, Pragma_Subprogram_Variant)));
      --  Only remove the defining axioms of expression functions which are
      --  recursive and have a numeric subprogram variant. The axiom has the
      --  form f params = expr which is always sound unless expr depends on f
      --  params, which should not be possible if f is not recursive or if it
      --  structurally terminates.

      S              : Why_Node_Sets.Set;
      Recursive_Only : Boolean :=
        Ekind (E) in E_Entry | E_Procedure | E_Function
        and then Is_Recursive (E);
      Own_Msg        : Unbounded_String;
      Continuations  : Message_Lists.List;
      --  Store continuations for mutually recursive functions whose contract
      --  might be unavailable to emit a warning. Recursive_Only is used to
      --  simplify the wording of the warning when the cycle is caused by
      --  recursion which should be the most common case.

   begin
      --  For recursive functions, include the module for the post axiom of
      --  mutually recursive subprograms if any.

      if Proof_Module_Cyclic (E) then
         for F of Proof_Cyclic_Functions loop
            if Proof_Module_Cyclic (E, F) then
               S.Insert (+Entity_Modules (F) (Fun_Post_Axiom));

               --  Remove the defining axioms of expression functions if needed

               if Remove_Expr_Fun_Body (F) then
                  S.Insert (+Entity_Modules (F) (Expr_Fun_Axiom));
               end if;

               --  If the subprogram has specializations, also include its
               --  specialized axioms.

               declare
                  use Node_Id_HO_Specializations_Map;
                  Position : constant Node_Id_HO_Specializations_Map.Cursor :=
                    M_HO_Specializations.Find (F);
               begin
                  if Position /= No_Element then
                     for Th of Element (Position) loop
                        S.Insert (+Th.Post_Module);
                     end loop;
                  end if;
               end;

               if Is_Dispatching_Operation (F)
                 and then not Is_Hidden_Dispatching_Operation (F)
               then
                  S.Insert (+Entity_Modules (F) (Dispatch_Post_Axiom));
               end if;

               if Entity_Body_In_SPARK (F)
                 and then Has_Contracts (F, Pragma_Refined_Post)
               then
                  S.Insert (+Entity_Modules (F) (Refined_Post_Axiom));
               end if;

               --  Store explanations about removed information in Own_Msg if
               --  F is E and Continuations otherwise.

               if Ekind (F) = E_Function then
                  declare
                     Has_Expr_Fun_Body      : constant Boolean :=
                       Remove_Expr_Fun_Body (F);
                     Has_Explicit_Contracts : constant Boolean :=
                       Has_Contracts (F, Pragma_Postcondition)
                       or else Has_Contracts (F, Pragma_Contract_Cases);
                     Has_Implicit_Contracts : constant Boolean :=
                       Type_Needs_Dynamic_Invariant (Etype (F));
                  begin

                     if Has_Expr_Fun_Body
                       or else Has_Implicit_Contracts
                       or else Has_Explicit_Contracts
                     then
                        if Unique_Entity (E) = Unique_Entity (F)
                          and then Is_Recursive (E)
                        then
                           Own_Msg :=
                             To_Unbounded_String
                               ((if Has_Expr_Fun_Body
                                 then
                                   "body "
                                   & (if Has_Implicit_Contracts
                                        or else Has_Explicit_Contracts
                                      then "and "
                                      else "")
                                 else "")
                                & (if Has_Explicit_Contracts
                                   then "contract "
                                   elsif Has_Implicit_Contracts
                                   then "implicit contract "
                                   else ""));
                        else
                           Recursive_Only :=
                             Recursive_Only and then Mutually_Recursive (E, F);

                           Continuations.Append
                             (Create
                                ("potentially missing "
                                 & (if Has_Expr_Fun_Body
                                    then
                                      "expression function body "
                                      & (if Has_Implicit_Contracts
                                           or else Has_Explicit_Contracts
                                         then "and "
                                         else "")
                                    else "")
                                 & (if Has_Explicit_Contracts
                                    then "contract "
                                    elsif Has_Implicit_Contracts
                                    then "implicit contract "
                                    else "")
                                 & "for & declared #",
                                 [F],
                                 Secondary_Loc => Sloc (F)));
                        end if;
                     end if;
                  end;
               end if;
            end if;
         end loop;
      end if;

      --  For all subprograms, include the axiom module of lemma functions
      --  if they are mutually recursive with the E taking into account the
      --  phantom link between a function and its lemma.

      for Lemma of Lemmas loop
         if Lemma_Module_Cyclic (Lemma, E) then
            S.Insert (+Entity_Modules (Lemma) (Lemma_Axiom));

            --  If the lemma is associated to a function which has
            --  specializations, also include its specialized axioms if any.

            declare
               use Node_Id_Modules_Map;
               Position : constant Node_Id_Modules_Map.Cursor :=
                 M_Lemma_HO_Specializations.Find (Lemma);
            begin
               if Position /= No_Element then
                  for M of Element (Position) loop
                     S.Insert (+M);
                  end loop;
               end if;
            end;

            --  For automatically instanciated lemmas, do not warn on the
            --  associated function or lemmas associated with the same
            --  function.

            declare
               F : constant Entity_Id :=
                 Unique_Entity
                   (Retrieve_Automatic_Instantiation_Annotation (Lemma));
            begin
               if Unique_Entity (Lemma) /= Unique_Entity (E)
                 and then Unique_Entity (E) /= F
                 and then
                   (not Has_Automatic_Instantiation_Annotation (E)
                    or else
                      Unique_Entity
                        (Retrieve_Automatic_Instantiation_Annotation (E))
                      /= F)
               then
                  Continuations.Append
                    (Create
                       ("potentially missing automatically instanciated lemma "
                        & "& declared #",
                        [Lemma],
                        Secondary_Loc => Sloc (Lemma)));

                  Recursive_Only :=
                    Recursive_Only and then Mutually_Recursive (E, F);
               end if;
            end;
         end if;
      end loop;

      --  If information might be lost due to proof cycles, emit a warning.
      --  Special case simply recursive functions.

      if Recursive_Only
        and then Length (Own_Msg) > 0
        and then Continuations.Is_Empty
      then
         Warning_Msg_N
           (Warn_Contracts_Recursive,
            E,
            Create
              ("& is recursive; its "
               & To_String (Own_Msg)
               & "might not be available on recursive calls from "
               & "contracts and assertions"
               & Tag_Suffix (Warn_Contracts_Recursive),
               [E]));

      --  General case: if any, add Own_Msg to the continuations and emit the
      --  standard message.

      elsif Length (Own_Msg) > 0 or not Continuations.Is_Empty then
         if Recursive_Only then
            if Length (Own_Msg) > 0 then
               Continuations.Prepend
                 (Create ("its " & To_String (Own_Msg) & "might be missing"));
            end if;

            Warning_Msg_N
              (Warn_Contracts_Recursive,
               E,
               Names         => [E],
               Continuations => Continuations);
         else
            if Length (Own_Msg) > 0 then
               Continuations.Prepend
                 (Create
                    ("the " & To_String (Own_Msg) & "of & might be missing",
                     [E]));
            end if;

            Warning_Msg_N
              (Warn_Proof_Module_Cyclic, E, Continuations => Continuations);
         end if;
      end if;

      return S;
   end Mutually_Recursive_Modules;

   -----------------------------------------------
   -- Register_Automatically_Instanciated_Lemma --
   -----------------------------------------------

   procedure Register_Automatically_Instanciated_Lemma (E : Entity_Id) is
   begin
      Lemmas.Include (E);
   end Register_Automatically_Instanciated_Lemma;

   ---------------------------------------
   -- Register_Function_With_Refinement --
   ---------------------------------------

   procedure Register_Function_With_Refinement (E : Entity_Id) is
   begin
      Functions_With_Refinement.Include (E);
   end Register_Function_With_Refinement;

   ------------------------------------
   -- Register_Proof_Cyclic_Function --
   ------------------------------------

   procedure Register_Proof_Cyclic_Function (E : Entity_Id) is
   begin
      Proof_Cyclic_Functions.Include (E);
   end Register_Proof_Cyclic_Function;

end Why.Atree.Modules;
