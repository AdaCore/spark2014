------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 S P A R K _ A T R E E . E N T I T I E S                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2022, AdaCore                     --
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

with Aspects;
with Checked_Types;          use Checked_Types;
with Einfo.Entities;
with Einfo.Utils;
with Sinfo.Nodes;
with Sem_Aux;
with SPARK_Util;
with SPARK_Util.Subprograms;

package SPARK_Atree.Entities is

   package EE renames Einfo.Entities;

   --  Renamings are either
   --  * trivial in the .ads file or
   --  * with Pre/Post contract completed-by-renaming in the .adb file.

   subtype Entity_Kind is EE.Entity_Kind;

   subtype Access_Kind          is EE.Access_Kind;
   subtype Array_Kind           is EE.Array_Kind;
   subtype Class_Wide_Kind      is EE.Class_Wide_Kind;
   subtype Constant_Or_Variable_Kind_Id is
     EE.Constant_Or_Variable_Kind_Id;
   subtype Composite_Kind       is EE.Composite_Kind;
   subtype Concurrent_Kind      is EE.Concurrent_Kind;
   subtype Discrete_Kind        is EE.Discrete_Kind;
   subtype Entry_Kind           is EE.Entry_Kind;
   subtype Enumeration_Kind     is EE.Enumeration_Kind;
   subtype Fixed_Point_Kind     is EE.Fixed_Point_Kind;
   subtype Float_Kind           is EE.Float_Kind;
   subtype Formal_Kind          is EE.Formal_Kind;
   subtype Integer_Kind         is EE.Integer_Kind;
   subtype Modular_Integer_Kind is EE.Modular_Integer_Kind;
   subtype Named_Kind           is EE.Named_Kind;
   subtype Object_Kind          is EE.Object_Kind;
   subtype Private_Kind         is EE.Private_Kind;
   subtype Protected_Kind       is EE.Protected_Kind;
   subtype Real_Kind            is EE.Real_Kind;
   subtype Record_Kind          is EE.Record_Kind;
   subtype Record_Field_Kind    is EE.Record_Field_Kind;
   subtype Scalar_Kind          is EE.Scalar_Kind;
   subtype Subprogram_Kind      is EE.Subprogram_Kind;
   subtype Task_Kind            is EE.Task_Kind;
   subtype Type_Kind            is EE.Type_Kind;

   subtype E_Constant_Id            is EE.E_Constant_Id;
   subtype E_Component_Id           is EE.E_Component_Id;
   subtype E_Discriminant_Id        is EE.E_Discriminant_Id;
   subtype E_Enumeration_Literal_Id is EE.E_Enumeration_Literal_Id;
   subtype E_In_Parameter_Id        is EE.E_In_Parameter_Id;
   subtype E_Loop_Id                is EE.E_Loop_Id;
   subtype E_Loop_Parameter_Id      is EE.E_Loop_Parameter_Id;
   subtype E_Function_Id            is EE.E_Function_Id;
   subtype E_Package_Id             is EE.E_Package_Id;
   subtype E_Package_Body_Id        is EE.E_Package_Body_Id;
   subtype E_Procedure_Id           is EE.E_Procedure_Id;
   subtype E_Protected_Type_Id      is EE.E_Protected_Type_Id;
   subtype E_Return_Statement_Id    is EE.E_Return_Statement_Id;
   subtype E_String_Literal_Subtype_Id is EE.E_String_Literal_Subtype_Id;
   subtype E_Subprogram_Type_Id     is EE.E_Subprogram_Type_Id;
   subtype E_Task_Type_Id           is EE.E_Task_Type_Id;

   subtype Opt_E_Constant_Id        is EE.Opt_E_Constant_Id;
   subtype Opt_E_Component_Id       is EE.Opt_E_Component_Id;
   subtype Opt_E_Discriminant_Id    is EE.Opt_E_Discriminant_Id;
   subtype Opt_E_Enumeration_Literal_Id is EE.Opt_E_Enumeration_Literal_Id;
   subtype Opt_E_In_Parameter_Id    is EE.Opt_E_In_Parameter_Id;
   subtype Opt_E_Loop_Id            is EE.Opt_E_Loop_Id;
   subtype Opt_E_Loop_Parameter_Id  is EE.Opt_E_Loop_Parameter_Id;
   subtype Opt_E_Function_Id        is EE.Opt_E_Function_Id;
   subtype Opt_E_Package_Id         is EE.Opt_E_Package_Id;
   subtype Opt_E_Package_Body_Id    is EE.Opt_E_Package_Body_Id;
   subtype Opt_E_Procedure_Id       is EE.Opt_E_Procedure_Id;
   subtype Opt_E_Protected_Type_Id  is EE.Opt_E_Protected_Type_Id;
   subtype Opt_E_Return_Statement_Id is EE.Opt_E_Return_Statement_Id;
   subtype Opt_E_String_Literal_Subtype_Id is
     EE.Opt_E_String_Literal_Subtype_Id;
   subtype Opt_E_Subprogram_Type_Id is EE.Opt_E_Subprogram_Type_Id;

   subtype Access_Kind_Id          is EE.Access_Kind_Id;
   subtype Array_Kind_Id           is EE.Array_Kind_Id;
   subtype Class_Wide_Kind_Id      is EE.Class_Wide_Kind_Id;
   subtype Composite_Kind_Id       is EE.Composite_Kind_Id;
   subtype Concurrent_Kind_Id      is EE.Concurrent_Kind_Id;
   subtype Discrete_Kind_Id        is EE.Discrete_Kind_Id;
   subtype Entry_Kind_Id           is EE.Entry_Kind_Id;
   subtype Enumeration_Kind_Id     is EE.Enumeration_Kind_Id;
   subtype Fixed_Point_Kind_Id     is EE.Fixed_Point_Kind_Id;
   subtype Float_Kind_Id           is EE.Float_Kind_Id;
   subtype Formal_Kind_Id          is EE.Formal_Kind_Id;
   subtype Integer_Kind_Id         is EE.Integer_Kind_Id;
   subtype Modular_Integer_Kind_Id is EE.Modular_Integer_Kind_Id;
   subtype Named_Kind_Id           is EE.Named_Kind_Id;
   subtype Object_Kind_Id          is EE.Object_Kind_Id;
   subtype Private_Kind_Id         is EE.Private_Kind_Id;
   subtype Protected_Kind_Id       is EE.Protected_Kind_Id;
   subtype Real_Kind_Id            is EE.Real_Kind_Id;
   subtype Record_Kind_Id          is EE.Record_Kind_Id;
   subtype Record_Field_Kind_Id    is EE.Record_Field_Kind_Id;
   subtype Scalar_Kind_Id          is EE.Scalar_Kind_Id;
   subtype Subprogram_Kind_Id      is EE.Subprogram_Kind_Id;
   subtype Task_Kind_Id            is EE.Task_Kind_Id;
   subtype Type_Kind_Id            is EE.Type_Kind_Id;

   subtype Opt_Access_Kind_Id          is EE.Opt_Access_Kind_Id;
   subtype Opt_Array_Kind_Id           is EE.Opt_Array_Kind_Id;
   subtype Opt_Class_Wide_Kind_Id      is EE.Opt_Class_Wide_Kind_Id;
   subtype Opt_Composite_Kind_Id       is EE.Opt_Composite_Kind_Id;
   subtype Opt_Concurrent_Kind_Id      is EE.Opt_Concurrent_Kind_Id;
   subtype Opt_Discrete_Kind_Id        is EE.Opt_Discrete_Kind_Id;
   subtype Opt_Entry_Kind_Id           is EE.Opt_Entry_Kind_Id;
   subtype Opt_Enumeration_Kind_Id     is EE.Opt_Enumeration_Kind_Id;
   subtype Opt_Fixed_Point_Kind_Id     is EE.Opt_Fixed_Point_Kind_Id;
   subtype Opt_Float_Kind_Id           is EE.Opt_Float_Kind_Id;
   subtype Opt_Formal_Kind_Id          is EE.Opt_Formal_Kind_Id;
   subtype Opt_Integer_Kind_Id         is EE.Opt_Integer_Kind_Id;
   subtype Opt_Modular_Integer_Kind_Id is EE.Opt_Modular_Integer_Kind_Id;
   subtype Opt_Named_Kind_Id           is EE.Opt_Named_Kind_Id;
   subtype Opt_Object_Kind_Id          is EE.Opt_Object_Kind_Id;
   subtype Opt_Private_Kind_Id         is EE.Opt_Private_Kind_Id;
   subtype Opt_Protected_Kind_Id       is EE.Opt_Protected_Kind_Id;
   subtype Opt_Real_Kind_Id            is EE.Opt_Real_Kind_Id;
   subtype Opt_Record_Kind_Id          is EE.Opt_Record_Kind_Id;
   subtype Opt_Record_Field_Kind_Id    is EE.Opt_Record_Field_Kind_Id;
   subtype Opt_Scalar_Kind_Id          is EE.Opt_Scalar_Kind_Id;
   subtype Opt_Subprogram_Kind_Id      is EE.Opt_Subprogram_Kind_Id;
   subtype Opt_Task_Kind_Id            is EE.Opt_Task_Kind_Id;
   subtype Opt_Type_Kind_Id            is EE.Opt_Type_Kind_Id;

   E_Abstract_State              : Entity_Kind renames
     EE.E_Abstract_State;
   E_Access_Subtype              : Entity_Kind renames
     EE.E_Access_Subtype;
   E_Access_Subprogram_Type      : Entity_Kind renames
     EE.E_Access_Subprogram_Type;
   E_Access_Type                 : Entity_Kind renames
     EE.E_Access_Type;
   E_Array_Subtype               : Entity_Kind renames
     EE.E_Array_Subtype;
   E_Array_Type                  : Entity_Kind renames
     EE.E_Array_Type;
   E_Class_Wide_Subtype          : Entity_Kind renames
     EE.E_Class_Wide_Subtype;
   E_Class_Wide_Type             : Entity_Kind renames
     EE.E_Class_Wide_Type;
   E_Component                   : Entity_Kind renames
     EE.E_Component;
   E_Constant                    : Entity_Kind renames
     EE.E_Constant;
   E_Discriminant                : Entity_Kind renames
     EE.E_Discriminant;
   E_Entry                       : Entity_Kind renames
     EE.E_Entry;
   E_Enumeration_Literal         : Entity_Kind renames
     EE.E_Enumeration_Literal;
   E_Exception_Type              : Entity_Kind renames
     EE.E_Exception_Type;
   E_Function                    : Entity_Kind renames
     EE.E_Function;
   E_General_Access_Type         : Entity_Kind renames
     EE.E_General_Access_Type;
   E_In_Parameter                : Entity_Kind renames
     EE.E_In_Parameter;
   E_In_Out_Parameter            : Entity_Kind renames
     EE.E_In_Out_Parameter;
   E_Incomplete_Subtype          : Entity_Kind renames
     EE.E_Incomplete_Subtype;
   E_Incomplete_Type             : Entity_Kind renames
     EE.E_Incomplete_Type;
   E_Label                       : Entity_Kind renames
     EE.E_Label;
   E_Loop_Parameter              : Entity_Kind renames
     EE.E_Loop_Parameter;
   E_Loop                        : Entity_Kind renames
     EE.E_Loop;
   E_Operator                    : Entity_Kind renames
     EE.E_Operator;
   E_Out_Parameter               : Entity_Kind renames
     EE.E_Out_Parameter;
   E_Package                     : Entity_Kind renames
     EE.E_Package;
   E_Package_Body                : Entity_Kind renames
     EE.E_Package_Body;
   E_Private_Subtype             : Entity_Kind renames
     EE.E_Private_Subtype;
   E_Procedure                   : Entity_Kind renames
     EE.E_Procedure;
   E_Protected_Type              : Entity_Kind renames
     EE.E_Protected_Type;
   E_Protected_Subtype           : Entity_Kind renames
     EE.E_Protected_Subtype;
   E_Task_Subtype                : Entity_Kind renames
     EE.E_Task_Subtype;
   E_Record_Subtype              : Entity_Kind renames
     EE.E_Record_Subtype;
   E_Record_Subtype_With_Private : Entity_Kind renames
     EE.E_Record_Subtype_With_Private;
   E_Record_Type                 : Entity_Kind renames
     EE.E_Record_Type;
   E_String_Literal_Subtype      : Entity_Kind renames
     EE.E_String_Literal_Subtype;
   E_Subprogram_Body             : Entity_Kind renames
     EE.E_Subprogram_Body;
   E_Subprogram_Type             : Entity_Kind renames
     EE.E_Subprogram_Type;
   E_Task_Type                   : Entity_Kind renames
     EE.E_Task_Type;
   E_Variable                    : Entity_Kind renames
     EE.E_Variable;
   E_Void                        : Entity_Kind renames
     EE.E_Void;

   function "=" (L, R : Entity_Kind) return Boolean renames
     EE."=";

   function Ekind (E : Entity_Id) return Entity_Kind renames
     EE.Ekind;

   function Get_Pragma (E : Entity_Id; Id : Pragma_Id) return Node_Id renames
     Einfo.Utils.Get_Pragma;

   function Is_Access_Subprogram_Type (E : Type_Kind_Id) return Boolean;
   --  Return True if E's base type is an access-to-subprogram type

   function Is_Access_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Access_Type;

   function Is_Access_Variable (E : Type_Kind_Id) return Boolean
     renames Sem_Util.Is_Access_Variable;

   function Is_Anonymous_Access_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Anonymous_Access_Type;

   function Is_Array_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Array_Type;

   function Is_Assignable (E : Object_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Assignable;

   function Is_Boolean_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Boolean_Type;

   function Is_Character_Type (E : Type_Kind_Id) return Boolean renames
     EE.Is_Character_Type;

   function Is_Compilation_Unit (E : Entity_Id) return Boolean renames
     EE.Is_Compilation_Unit;

   function Is_Composite_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Composite_Type;

   function Is_Concurrent_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Concurrent_Type;

   function Is_Constant_Object (E : Object_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Constant_Object;

   function Is_Discriminal (E : Object_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Discriminal;

   function Is_Discrete_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Discrete_Type;

   function Is_Double_Precision_Floating_Point_Type
     (E : Type_Kind_Id)
      return Boolean
   renames Sem_Util.Is_Double_Precision_Floating_Point_Type;

   function Is_Elementary_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Elementary_Type;

   function Is_Entity_Name (N : Node_Id) return Boolean with
     Post => not Is_Entity_Name'Result
       or else (Nkind (N) in N_Has_Entity and then Present (Entity (N)));

   function Is_Entry (E : Entity_Id) return Boolean renames
     Einfo.Utils.Is_Entry;

   function Is_Enumeration_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Enumeration_Type;

   function Is_Extended_Precision_Floating_Point_Type
     (E : Type_Kind_Id)
      return Boolean
   renames Sem_Util.Is_Extended_Precision_Floating_Point_Type;

   function Is_Fixed_Point_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Fixed_Point_Type;

   function Is_Floating_Point_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Floating_Point_Type;

   function Is_Formal (E : Object_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Formal;

   function Is_Generic_Unit (E : Entity_Id) return Boolean renames
     Einfo.Utils.Is_Generic_Unit;

   function Is_Imported (E : Entity_Id) return Boolean renames
     EE.Is_Imported;

   function Is_Itype (E : Type_Kind_Id) return Boolean renames
     EE.Is_Itype;

   function Is_Library_Level_Entity (E : Entity_Id) return Boolean renames
     Sem_Util.Is_Library_Level_Entity;

   function Is_Modular_Integer_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Modular_Integer_Type;

   function Is_Named_Number (E : Object_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Named_Number;

   function Is_Object (E : Entity_Id) return Boolean renames
     Einfo.Utils.Is_Object;

   function Is_Private_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Private_Type;

   function Is_Protected_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Protected_Type;

   function Is_Record_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Record_Type;

   function Is_Scalar_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Scalar_Type;

   function Is_Signed_Integer_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_Signed_Integer_Type;

   function Is_String_Type (E : Type_Kind_Id) return Boolean renames
     Einfo.Utils.Is_String_Type;

   function Is_Single_Precision_Floating_Point_Type
     (E : Type_Kind_Id)
      return Boolean
   renames Sem_Util.Is_Single_Precision_Floating_Point_Type;

   function Is_Subprogram (E : Entity_Id) return Boolean renames
     Einfo.Utils.Is_Subprogram;

   function Is_Subprogram_Or_Entry (E : Entity_Id) return Boolean renames
     Einfo.Utils.Is_Subprogram_Or_Entry;

   function Is_Task_Type (E : Entity_Id) return Boolean renames
     Einfo.Utils.Is_Task_Type;

   function Is_Type (E : Entity_Id) return Boolean renames Einfo.Utils.Is_Type;

   function Is_Unchecked_Union (E : Type_Kind_Id) return Boolean;
   --  Same as Einfo.Is_Unchecked_Union except that it goes to the Base_Retysp

   function Is_Universal_Numeric_Type (E : Type_Kind_Id) return Boolean renames
     Sem_Util.Is_Universal_Numeric_Type;

   function Unique_Entity (E : Entity_Id) return Entity_Id renames
     Sem_Util.Unique_Entity;

   function Within_Protected_Type (E : Entity_Id) return Boolean renames
     Sem_Util.Within_Protected_Type;

   ----------------
   --  For Types --
   ----------------

   function Associated_Node_For_Itype (Id : Type_Kind_Id) return Node_Id;

   function Base_Type (Typ : Type_Kind_Id) return Entity_Id;

   function Cloned_Subtype (Typ : Type_Kind_Id) return Entity_Id;

   function Get_Cursor_Type (Typ : Type_Kind_Id) return Entity_Id
     with Pre =>
       Present (Aspects.Find_Aspect (Typ, A => Aspects.Aspect_Iterable));

   function Get_Iterable_Type_Primitive
     (Typ : Type_Kind_Id;
      Nam : Name_Id)
      return E_Function_Id
   with Pre  => Nam in Name_Element
                     | Name_First
                     | Name_Has_Element
                     | Name_Last
                     | Name_Next
                     | Name_Previous,
        Post => Get_Iterable_Type_Primitive'Result =
                Sem_Aux.Ultimate_Alias (Get_Iterable_Type_Primitive'Result);

   function Has_Default_Aspect (Typ : Type_Kind_Id) return Boolean;
   --  Same as EE.Has_Default_Aspect except that it goes to the
   --  Base_Retysp.

   function Has_DIC (Typ : Type_Kind_Id) return Boolean;

   function Has_Predicates (Typ : Type_Kind_Id) return Boolean;

   function Invariant_Procedure (Typ : Type_Kind_Id) return Opt_E_Procedure_Id
     with Post =>
       (if Present (Invariant_Procedure'Result) then
          Einfo.Utils.Number_Formals (Invariant_Procedure'Result) = 1);

   function Is_Actual_Subtype (Typ : Type_Kind_Id) return Boolean
     renames Einfo.Entities.Is_Actual_Subtype;

   function Is_Base_Type (Typ : Type_Kind_Id) return Boolean;

   function Is_Class_Wide_Type (Typ : Type_Kind_Id) return Boolean;

   function Is_Constrained (Typ : Type_Kind_Id) return Boolean;

   function Is_Fixed_Lower_Bound_Array_Subtype
     (Typ : Type_Kind_Id)
      return Boolean
     renames Einfo.Entities.Is_Fixed_Lower_Bound_Array_Subtype;

   function Is_Fixed_Lower_Bound_Index_Subtype
     (Typ : Type_Kind_Id)
      return Boolean
     renames Einfo.Entities.Is_Fixed_Lower_Bound_Index_Subtype;

   function Is_Limited_View (Typ : Type_Kind_Id) return Boolean;

   function Is_Tagged_Type (Typ : Type_Kind_Id) return Boolean;

   function Known_Object_Size (Typ : Type_Kind_Id) return Boolean;
   --  Renaming of Einfo.Known_Esize

   function Object_Size (Typ : Type_Kind_Id) return Uint
     with Pre => Known_Object_Size (Typ);
   --  Renaming of Einfo.Esize

   function Partial_DIC_Procedure
     (Typ : Type_Kind_Id)
      return Opt_E_Procedure_Id
   with
     Post =>
         (if Present (Partial_DIC_Procedure'Result) then
            Einfo.Utils.Number_Formals (Partial_DIC_Procedure'Result) = 1);

   function Predicate_Function (Typ : Type_Kind_Id) return Opt_E_Function_Id
     with Post =>
       (if Present (Predicate_Function'Result) then
          Einfo.Utils.Number_Formals (Predicate_Function'Result) = 1);

   function Ultimate_Ancestor (Typ : Type_Kind_Id) return Type_Kind_Id;
   --  Return the ultimate ancestor of a type (the fisrt subtype of its root
   --  type.

   -----------------------
   --  For Scalar Types --
   -----------------------

   function Default_Aspect_Value
     (Typ : Scalar_Kind_Id)
      return Opt_N_Subexpr_Id;
   --  Same as Einfo.Default_Aspect_Value except that it goes to the
   --  Base_Retysp.

   function Max_Size_Of_Img_Attr (Typ : Scalar_Kind_Id) return Uint;
   --  Return the maximal size of 'Image for type Typ

   function Type_High_Bound (Typ : Scalar_Kind_Id) return Opt_N_Subexpr_Id;

   function Type_Low_Bound (Typ : Entity_Id) return Opt_N_Subexpr_Id with
     Pre => Is_Scalar_Type (Typ)
       or else Ekind (Typ) = E_String_Literal_Subtype;
   --  Same as Einfo.Type_Low_Bound except that it accepts string literal
   --  subtypes and returns String_Literal_Low_Bound so that it can be called
   --  on the result of SPARK_Util.Nth_Index_Type which may return a string
   --  literal subtype.

   ----------------------------
   --  For Enumeration Types --
   ----------------------------

   function Enumeration_Pos (Obj : E_Enumeration_Literal_Id) return Uint
     renames Einfo.Entities.Enumeration_Pos;

   function Enumeration_Rep (Obj : E_Enumeration_Literal_Id) return Uint
     renames Einfo.Entities.Enumeration_Rep;

   function Has_Enumeration_Rep_Clause
     (Typ : Enumeration_Kind_Id)
      return Boolean
     renames Einfo.Entities.Has_Enumeration_Rep_Clause;

   function First_Literal
     (Typ : Enumeration_Kind_Id)
      return E_Enumeration_Literal_Id
     renames Einfo.Entities.First_Literal;

   function Next_Literal
     (E : E_Enumeration_Literal_Id)
      return Opt_E_Enumeration_Literal_Id
      renames Einfo.Utils.Next_Literal;

   procedure Next_Literal (E : in out Opt_E_Enumeration_Literal_Id) renames
     Einfo.Utils.Next_Literal;

   function Get_Enum_Lit_From_Pos
     (Typ : Enumeration_Kind_Id;
      P   : Uint)
      return Node_Id
   with
     Post => Nkind (Get_Enum_Lit_From_Pos'Result) in N_Identifier
                                                   | N_Character_Literal;
   --  Same as Sum_Util.Get_Enum_Lit_From_Pos except that Loc parameter is
   --  always No_Location.

   --------------------------------
   --  For Modular Integer Types --
   --------------------------------

   function Modular_Size (Typ : Modular_Integer_Kind_Id) return Uint;
   --  Out of 8, 16, 32, 64 and 128, return the smallest X such that 2 ** X is
   --  greater or equal to the modulus of the type. This is basically used to
   --  determine the bitvector used for proof. Note that this can be different
   --  from the Ada RM Size of the type, which can be changed via a Size
   --  declaration.

   function Modulus (Typ : Modular_Integer_Kind_Id) return Uint;
   --  Same as Einfo.Modulus except that it goes to the Base_Retysp

   function Non_Binary_Modulus (Typ : Modular_Integer_Kind_Id) return Boolean;
   --  Same as Einfo.Non_Binary_Modulus except that it goes to the Base_Retysp

   ----------------------------
   --  For Fixed Point Types --
   ----------------------------

   function Small_Value (Typ : Fixed_Point_Kind_Id) return Ureal
     renames Einfo.Entities.Small_Value;

   ------------------
   --  For Records --
   ------------------

   function Discriminant_Constraint (Typ : Type_Kind_Id) return Elist_Id
     with Pre => Has_Discriminants (Typ);

   function Has_Defaulted_Discriminants (Typ : Type_Kind_Id) return Boolean;

   function Has_Discriminants (Typ : Type_Kind_Id) return Boolean;
   --  Same as Einfo.Has_Discriminants except that it ignores hidden
   --  discriminants.

   function First_Discriminant (Typ : Type_Kind_Id) return E_Discriminant_Id
   with
     Pre  => Has_Discriminants (Typ),
     Post => SPARK_Util.Is_Not_Hidden_Discriminant (First_Discriminant'Result);
   --  Same as Sem_Aux.First_Discriminants

   procedure Next_Discriminant (Discr : in out Opt_E_Discriminant_Id)
     with Post => (if Present (Discr) then
                     SPARK_Util.Is_Not_Hidden_Discriminant (Discr));
   --  Same as Einfo.Next_Discriminants

   function Stored_Constraint (Typ : Type_Kind_Id) return Elist_Id
     with Pre => Ekind (Typ) in Record_Kind
                              | Concurrent_Kind
                              | Private_Kind;

   --------------------------
   --  For Protected Types --
   --------------------------

   function Has_Attach_Handler (Typ : E_Protected_Type_Id) return Boolean;

   function Has_Interrupt_Handler (Typ : E_Protected_Type_Id) return Boolean;

   -----------------
   --  For Arrays --
   -----------------

   function Component_Type (Typ : Array_Kind_Id) return Type_Kind_Id
     renames Einfo.Entities.Component_Type;

   function Default_Aspect_Component_Value
     (Typ : Array_Kind_Id)
      return Opt_N_Subexpr_Id;
   --  Same as Einfo.Default_Aspect_Component_Value except that it goes to the
   --  Base_Retysp.

   function First_Index (Typ : Array_Kind_Id) return Node_Id
     renames Einfo.Entities.First_Index;

   procedure Next_Index (Index : in out Node_Id) renames
     Einfo.Utils.Next_Index;

   function Next_Index (Index : Node_Id) return Node_Id
     renames Einfo.Utils.Next_Index;

   function Number_Dimensions (Typ : Array_Kind_Id) return Pos;

   ------------------
   --  For Strings --
   ------------------

   function String_Literal_Length
     (Typ : E_String_Literal_Subtype_Id)
      return Uint
     renames Einfo.Entities.String_Literal_Length;

   function String_Literal_Low_Bound
     (Typ : E_String_Literal_Subtype_Id)
      return Node_Id
     renames Einfo.Entities.String_Literal_Low_Bound;

   -----------------------
   --  For Access Types --
   -----------------------

   function Designates_Incomplete_Type (E : Access_Kind_Id) return Boolean;
   --  Returns True if E is an access type which designates an incomplete type
   --  or a partial view of a type.

   function Directly_Designated_Type (E : Access_Kind_Id) return Type_Kind_Id;
   --  If E designates an incomplete type, return its full view, else return
   --  the designated type.

   function Can_Never_Be_Null (E : Access_Kind_Id) return Boolean renames
     EE.Can_Never_Be_Null;

   function Is_Access_Constant (E : Access_Kind_Id) return Boolean renames
     EE.Is_Access_Constant;

   function Access_Subprogram_Wrapper
     (E : E_Subprogram_Type_Id)
      return Opt_Subprogram_Kind_Id
   is (EE.Access_Subprogram_Wrapper (E));

   ------------------
   --  For Objects --
   ------------------

   function Actual_Subtype (Obj : Object_Kind_Id) return Opt_Type_Kind_Id;

   function Component_Clause (Obj : Record_Field_Kind_Id) return Node_Id
     renames Einfo.Entities.Component_Clause;

   function Constant_Value (Obj : E_Constant_Id) return N_Subexpr_Id;

   function Discriminal_Link (Obj : Object_Kind_Id) return E_Discriminant_Id
     with Pre => Is_Discriminal (Obj);

   function Discriminant_Default_Value
     (Obj : E_Discriminant_Id)
      return Opt_N_Subexpr_Id;

   function Enclosing_Type (Obj : Entity_Id) return Type_Kind_Id with
     Pre  => Ekind (Obj) in
       E_Discriminant | E_Component | E_Constant | E_In_Parameter
        or else SPARK_Util.Subprograms.Is_Protected_Operation (Obj),
     Post => Ekind (Enclosing_Type'Result) in
       Record_Kind | Private_Kind | Concurrent_Kind;
   --  Return the scope of a record component, discriminant, discriminal or
   --  protected operation.

   function Full_View (Obj : E_Constant_Id) return E_Constant_Id
     with Pre => SPARK_Util.Is_Partial_View (Obj);

   function Is_Aliased (Obj : E_In_Parameter_Id) return Boolean;

   function Known_Component_First_Bit
     (Obj : Record_Field_Kind_Id)
      return Boolean;
   --  Returns True if the first bit of a component has been supplied either
   --  through a component clause or directly.

   function Known_Component_Last_Bit
     (Obj : Record_Field_Kind_Id)
      return Boolean;
   --  Returns True if the last bit of a component has been supplied either
   --  through a component clause or through appropriate offset and component
   --  size.

   ----------------------
   --  For Subprograms --
   ----------------------

   function First_Formal (Subp : Callable_Kind_Id) return Opt_Formal_Kind_Id;
   --  Same as Einfo.Utils.First_Formal except that it ignores the formal
   --  introduced for the access-to-subprogram object in access subprogram
   --  wrappers.

   function Number_Formals (Subp : Callable_Kind_Id) return Natural;
   --  Same as Einfo.Utils.Number_Formals except that it ignores the formal
   --  introduced for the access-to-subprogram object in access subprogram
   --  wrappers.

   function Has_Controlling_Result (Subp : E_Function_Id) return Boolean;

   function Has_Pragma_Volatile_Function
     (Subp : Callable_Kind_Id)
      return Boolean;
   --  Return True if Subp has a pragma Volatile_Function or if it is an
   --  unchecked conversion with a volatile profile.
   --  This is different from Sem_Util.Is_Volatile_Function as it does not
   --  return True for protected functions.

   function Is_Expression_Function_Or_Completion
     (Subp : Callable_Kind_Id)
      return Boolean;

   function Is_Predicate_Function (Subp : Subprogram_Kind_Id) return Boolean;

   function Is_Visible_Dispatching_Operation
     (Subp : Callable_Kind_Id)
      return Boolean;
   --  Return True if Subp is a dispatching operation and there is a visibly
   --  tagged dispatching type (SPARK_Util.Subprograms.Find_Dispatching_Type
   --  returns True).

   function Next_Formal (Formal : Formal_Kind_Id) return Opt_Formal_Kind_Id;
   --  Same as Einfo.Utils.Next_Formal except that it ignores the formal
   --  introduced for the access-to-subprogram object in access subprogram
   --  wrappers.

   procedure Next_Formal (Formal : in out Opt_Formal_Kind_Id);
   --  Same as Einfo.Utils.Next_Formal except that it ignores the formal
   --  introduced for the access-to-subprogram object in access subprogram
   --  wrappers.

   function No_Return (Subp : Callable_Kind_Id) return Boolean renames
     EE.No_Return;

   function Null_Present (Subp : E_Procedure_Id) return Boolean;
   --  Applies Sinfo.Null_Present on the specification of Subp

   function Is_Unchecked_Conversion_Instance
     (Subp : Callable_Kind_Id)
      return Boolean;
   --  Same as Sem_Util.Is_Unchecked_Conversion_Instance

   function Overridden_Operation
     (E : Subprogram_Kind_Id)
      return Opt_Subprogram_Kind_Id;
   --  Same as Einfo.Entities.Overridden_Operation except that it goes to the
   --  ultimate alias.

   -------------------
   --  For Packages --
   -------------------

   function Is_Wrapper_Package (Pack : E_Package_Id) return Boolean;

   function Package_Body_Entity
     (Pack : N_Package_Body_Id)
      return E_Package_Body_Id;

   function Package_Body
     (Pack : E_Package_Id)
      return Opt_N_Package_Body_Id;

   function Private_Declarations_Of_Package
     (Pack : E_Package_Id)
      return List_Id;
   --  @return the list of private declarations of the package

   function Visible_Declarations_Of_Package
     (Pack : E_Package_Id)
      return List_Id;
   --  @return the list of visible declarations of the package

   -------------------------
   --  For other entities --
   -------------------------

   function Alignment (Ent : Entity_Id) return Unat with
     Pre => (Is_Type (Ent) or else Is_Object (Ent))
       and then Known_Alignment (Ent);

   function Enclosing_Declaration (E : Entity_Id) return Node_Id with
     Pre  => Is_Object (E) or else Is_Named_Number (E) or else Is_Type (E),
     Post => Nkind (Enclosing_Declaration'Result) in
         Sinfo.Nodes.N_Declaration
       | Sinfo.Nodes.N_Later_Decl_Item
       | Sinfo.Nodes.N_Number_Declaration;
   --  Special case of Sem_Util.Enclosing_Declaration where only one call to
   --  Parent is needed.

   function Get_Rep_Item (E : Entity_Id; Nam : Name_Id) return Node_Id with
     Pre => Ekind (E) in Protected_Kind |
                         E_Function     |
                         E_Procedure    |
                         E_Task_Type
         and then Nam in Name_Priority | Name_Interrupt_Priority;

   function Known_Alignment (Ent : Entity_Id) return Boolean with
     Pre => Is_Type (Ent) or else Is_Object (Ent);

   function Known_To_Precede (Withed, Main : Entity_Id) return Boolean with
     Pre => Is_Compilation_Unit (Withed)
       and then Is_Compilation_Unit (Main);
   --  Computed whether library unit [Withed] precedes library unit [Main] as
   --  defined in SPARK RM 7.7(2).

   function Return_Applies_To (E : E_Return_Statement_Id) return Node_Id;

end SPARK_Atree.Entities;
