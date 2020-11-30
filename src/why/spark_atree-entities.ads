------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 S P A R K _ A T R E E . E N T I T I E S                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2020, AdaCore                     --
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
with Einfo;      use Einfo;
with Sem_Aux;
with SPARK_Util;

package SPARK_Atree.Entities is

   --  Renamings are either
   --  * trivial in the .ads file or
   --  * with Pre/Post contract completed-by-renaming in the .adb file.

   subtype Entity_Kind is Einfo.Entity_Kind;

   subtype Access_Kind      is Einfo.Access_Kind;
   subtype Array_Kind       is Einfo.Array_Kind;
   subtype Class_Wide_Kind  is Einfo.Class_Wide_Kind;
   subtype Composite_Kind   is Einfo.Composite_Kind;
   subtype Concurrent_Kind  is Einfo.Concurrent_Kind;
   subtype Discrete_Kind    is Einfo.Discrete_Kind;
   subtype Entry_Kind       is Einfo.Entry_Kind;
   subtype Fixed_Point_Kind is Einfo.Fixed_Point_Kind;
   subtype Float_Kind       is Einfo.Float_Kind;
   subtype Formal_Kind      is Einfo.Formal_Kind;
   subtype Integer_Kind     is Einfo.Integer_Kind;
   subtype Named_Kind       is Einfo.Named_Kind;
   subtype Object_Kind      is Einfo.Object_Kind;
   subtype Private_Kind     is Einfo.Private_Kind;
   subtype Protected_Kind   is Einfo.Protected_Kind;
   subtype Real_Kind        is Einfo.Real_Kind;
   subtype Record_Kind      is Einfo.Record_Kind;
   subtype Scalar_Kind      is Einfo.Scalar_Kind;
   subtype Subprogram_Kind  is Einfo.Subprogram_Kind;
   subtype Task_Kind        is Einfo.Task_Kind;
   subtype Type_Kind        is Einfo.Type_Kind;

   E_Abstract_State              : Entity_Kind renames Einfo.E_Abstract_State;
   E_Access_Subtype              : Entity_Kind renames Einfo.E_Access_Subtype;
   E_Access_Subprogram_Type      : Entity_Kind renames
     Einfo.E_Access_Subprogram_Type;
   E_Access_Type                 : Entity_Kind renames Einfo.E_Access_Type;
   E_Array_Subtype               : Entity_Kind renames Einfo.E_Array_Subtype;
   E_Array_Type                  : Entity_Kind renames Einfo.E_Array_Type;
   E_Class_Wide_Subtype          : Entity_Kind renames
     Einfo.E_Class_Wide_Subtype;
   E_Class_Wide_Type             : Entity_Kind renames Einfo.E_Class_Wide_Type;
   E_Component                   : Entity_Kind renames Einfo.E_Component;
   E_Constant                    : Entity_Kind renames Einfo.E_Constant;
   E_Discriminant                : Entity_Kind renames Einfo.E_Discriminant;
   E_Entry                       : Entity_Kind renames Einfo.E_Entry;
   E_Enumeration_Literal         : Entity_Kind renames
     Einfo.E_Enumeration_Literal;
   E_Exception_Type              : Entity_Kind renames Einfo.E_Exception_Type;
   E_Function                    : Entity_Kind renames
     Einfo.E_Function;
   E_In_Parameter                : Entity_Kind renames Einfo.E_In_Parameter;
   E_In_Out_Parameter            : Entity_Kind renames
     Einfo.E_In_Out_Parameter;
   E_Incomplete_Subtype          : Entity_Kind renames
     Einfo.E_Incomplete_Subtype;
   E_Incomplete_Type             : Entity_Kind renames Einfo.E_Incomplete_Type;
   E_Label                       : Entity_Kind renames Einfo.E_Label;
   E_Loop_Parameter              : Entity_Kind renames Einfo.E_Loop_Parameter;
   E_Loop                        : Entity_Kind renames Einfo.E_Loop;
   E_Operator                    : Entity_Kind renames Einfo.E_Operator;
   E_Out_Parameter               : Entity_Kind renames Einfo.E_Out_Parameter;
   E_Package                     : Entity_Kind renames Einfo.E_Package;
   E_Package_Body                : Entity_Kind renames Einfo.E_Package_Body;
   E_Private_Subtype             : Entity_Kind renames Einfo.E_Private_Subtype;
   E_Procedure                   : Entity_Kind renames Einfo.E_Procedure;
   E_Protected_Type              : Entity_Kind renames Einfo.E_Protected_Type;
   E_Protected_Subtype           : Entity_Kind renames
     Einfo.E_Protected_Subtype;
   E_Task_Subtype                : Entity_Kind renames Einfo.E_Task_Subtype;
   E_Record_Subtype              : Entity_Kind renames Einfo.E_Record_Subtype;
   E_Record_Subtype_With_Private : Entity_Kind renames
     Einfo.E_Record_Subtype_With_Private;
   E_Record_Type                 : Entity_Kind renames Einfo.E_Record_Type;
   E_String_Literal_Subtype      : Entity_Kind renames
     Einfo.E_String_Literal_Subtype;
   E_Subprogram_Body             : Entity_Kind renames Einfo.E_Subprogram_Body;
   E_Subprogram_Type             : Entity_Kind renames Einfo.E_Subprogram_Type;
   E_Task_Type                   : Entity_Kind renames Einfo.E_Task_Type;
   E_Variable                    : Entity_Kind renames Einfo.E_Variable;
   E_Void                        : Entity_Kind renames Einfo.E_Void;

   function "=" (L, R : Entity_Kind) return Boolean renames Einfo."=";

   function Ekind (E : Entity_Id) return Entity_Kind renames Atree.Ekind;

   function Get_Pragma (E : Entity_Id; Id : Pragma_Id) return Node_Id renames
     Einfo.Get_Pragma;

   function Is_Access_Subprogram_Type (E : Entity_Id) return Boolean;
   --  Return True if E's base type is an access-to-subprogram type

   function Is_Access_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Access_Type;

   function Is_Anonymous_Access_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Anonymous_Access_Type;

   function Is_Array_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Array_Type;

   function Is_Assignable (E : Entity_Id) return Boolean renames
     Einfo.Is_Assignable;

   function Is_Boolean_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Boolean_Type;

   function Is_Character_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Character_Type;

   function Is_Compilation_Unit (E : Entity_Id) return Boolean renames
     Einfo.Is_Compilation_Unit;

   function Is_Composite_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Composite_Type;

   function Is_Concurrent_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Concurrent_Type;

   function Is_Constant_Object (E : Entity_Id) return Boolean renames
     Einfo.Is_Constant_Object;

   function Is_Discriminal (E : Entity_Id) return Boolean renames
     Einfo.Is_Discriminal;

   function Is_Discrete_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Discrete_Type;

   function Is_Double_Precision_Floating_Point_Type
     (E : Entity_Id) return Boolean
     renames Sem_Util.Is_Double_Precision_Floating_Point_Type;

   function Is_Elementary_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Elementary_Type;

   function Is_Entity_Name (N : Node_Id) return Boolean with
     Post => not Is_Entity_Name'Result
     or else (Nkind (N) in N_Has_Entity and then Present (Entity (N)));

   function Is_Entry (E : Entity_Id) return Boolean renames
     Einfo.Is_Entry;

   function Is_Enumeration_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Enumeration_Type;

   function Is_Fixed_Point_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Fixed_Point_Type;

   function Is_Floating_Point_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Floating_Point_Type;

   function Is_Formal (E : Entity_Id) return Boolean renames Einfo.Is_Formal;

   function Is_Generic_Unit (E : Entity_Id) return Boolean renames
     Einfo.Is_Generic_Unit;

   function Is_Itype (E : Entity_Id) return Boolean renames
     Einfo.Is_Itype;

   function Is_Library_Level_Entity (E : Entity_Id) return Boolean renames
     Sem_Util.Is_Library_Level_Entity;

   function Is_Modular_Integer_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Modular_Integer_Type;

   function Is_Named_Number (E : Entity_Id) return Boolean renames
     Einfo.Is_Named_Number;

   function Is_Object (E : Entity_Id) return Boolean renames Einfo.Is_Object;

   function Is_Private_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Private_Type;

   function Is_Protected_Operation (E : Entity_Id) return Boolean renames
     Sem_Aux.Is_Protected_Operation;

   function Is_Protected_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Protected_Type;

   function Is_Record_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Record_Type;

   function Is_Scalar_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Scalar_Type;

   function Is_Signed_Integer_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Signed_Integer_Type;

   function Is_String_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_String_Type;

   function Is_Single_Precision_Floating_Point_Type
     (E : Entity_Id) return Boolean
     renames Sem_Util.Is_Single_Precision_Floating_Point_Type;

   function Is_Subprogram (E : Entity_Id) return Boolean renames
     Einfo.Is_Subprogram;

   function Is_Subprogram_Or_Entry (E : Entity_Id) return Boolean renames
     Einfo.Is_Subprogram_Or_Entry;

   function Is_Task_Type (E : Entity_Id) return Boolean renames
     Einfo.Is_Task_Type;

   function Is_Type (E : Entity_Id) return Boolean renames Einfo.Is_Type;

   function Is_Universal_Numeric_Type (E : Entity_Id) return Boolean renames
     Sem_Util.Is_Universal_Numeric_Type;

   function Is_Imported (E : Entity_Id) return Boolean renames
     Einfo.Is_Imported;

   function Unique_Entity (E : Entity_Id) return Entity_Id renames
     Sem_Util.Unique_Entity;

   function Within_Protected_Type (E : Entity_Id) return Boolean renames
     Sem_Util.Within_Protected_Type;

   ----------------
   --  For Types --
   ----------------

   function Associated_Node_For_Itype (Id : Entity_Id) return Node_Id with
     Pre => Is_Itype (Id);

   function Base_Type (Typ : Entity_Id) return Entity_Id with
     Pre => Is_Type (Typ);

   function Cloned_Subtype (Typ : Entity_Id) return Entity_Id with
     Pre => Is_Type (Typ);

   function First_Subtype (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Type (Typ),
     Post => Einfo.Is_First_Subtype (First_Subtype'Result);

   function Get_Cursor_Type (Typ : Entity_Id) return Entity_Id with
     Pre => Is_Type (Typ)
     and then Present (Aspects.Find_Aspect
                       (Typ, A => Aspects.Aspect_Iterable));

   function Get_Iterable_Type_Primitive
     (Typ : Entity_Id;
      Nam : Name_Id)
      return Entity_Id
   with Pre  => Is_Type (Typ)
                  and then
                Nam in Name_Element
                     | Name_First
                     | Name_Has_Element
                     | Name_Last
                     | Name_Next
                     | Name_Previous,
        Post => Ekind (Get_Iterable_Type_Primitive'Result) = E_Function
                  and then
                Get_Iterable_Type_Primitive'Result =
                Sem_Aux.Ultimate_Alias (Get_Iterable_Type_Primitive'Result);

   function Get_User_Defined_Eq (Typ : Entity_Id) return Entity_Id with
     Pre => Is_Type (Typ);
   --  Same as Einfo.Get_User_Defined_Eq except that it goes through renamings

   function Has_Default_Aspect (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);
   --  Same as Einfo.Has_Default_Aspect except that it goes to the Base_Retysp

   function Has_DIC (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Has_Own_DIC (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Has_Predicates (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Invariant_Procedure (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Type (Typ),
     Post => (if Present (Invariant_Procedure'Result) then
                  Ekind (Invariant_Procedure'Result) = E_Procedure
                  and then
                   Einfo.Number_Formals (Invariant_Procedure'Result) = 1);

   function Is_Actual_Subtype (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Is_Base_Type (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Is_Class_Wide_Type (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Is_Constrained (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Is_Limited_View (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Is_Tagged_Type (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Known_Object_Size (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);
   --  Renaming of Einfo.Known_Esize

   function Object_Size (Typ : Entity_Id) return Uint with
     Pre => Is_Type (Typ) and then Known_Object_Size (Typ);
   --  Renaming of Einfo.Esize

   function Partial_DIC_Procedure (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Type (Typ),
     Post => (if Present (Partial_DIC_Procedure'Result) then
                  Ekind (Partial_DIC_Procedure'Result) = E_Procedure
                  and then
                     Einfo.Number_Formals (Partial_DIC_Procedure'Result) = 1);

   function Predicate_Function (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Type (Typ),
     Post => (if Present (Predicate_Function'Result) then
                  Ekind (Predicate_Function'Result) = E_Function
                  and then
                     Einfo.Number_Formals (Predicate_Function'Result) = 1);

   function Ultimate_Ancestor (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Type (Typ),
     Post => Is_Type (Ultimate_Ancestor'Result);
   --  Return the ultimate ancestor of a type (the fisrt subtype of its root
   --  type.

   -----------------------
   --  For Scalar Types --
   -----------------------

   function Default_Aspect_Value (Typ : Entity_Id) return Node_Id with
     Pre => Is_Scalar_Type (Typ);
   --  Same as Einfo.Default_Aspect_Value except that it goes to the
   --  Base_Retysp.

   function Type_High_Bound (Typ : Entity_Id) return Node_Id with
     Pre => Is_Scalar_Type (Typ);

   function Max_Size_Of_Img_Attr (Typ : Entity_Id) return Uint with
     Pre => Is_Scalar_Type (Typ);
   --  Return the maximal size of 'Image for type Typ

   function Type_Low_Bound (Typ : Entity_Id) return Node_Id with
     Pre => Is_Scalar_Type (Typ)
     or else Ekind (Typ) = E_String_Literal_Subtype;
   --  Same as Einfo.Type_Low_Bound except that it accepts string literal
   --  subtypes and returns String_Literal_Low_Bound so that it can be called
   --  on the result of SPARK_Util.Nth_Index_Type which may return a string
   --  literal subtype.

   ----------------------------
   --  For Enumeration Types --
   ----------------------------

   function Has_Enumeration_Rep_Clause (Typ : Entity_Id) return Boolean
   with
     Pre  => Is_Enumeration_Type (Typ);

   function First_Literal (Typ : Entity_Id) return Entity_Id
   with
     Pre  => Is_Enumeration_Type (Typ);

   function Next_Literal (E : Entity_Id) return Entity_Id renames
     Einfo.Next_Literal;

   procedure Next_Literal (E : in out Entity_Id) renames
     Einfo.Next_Literal;

   function Get_Enum_Lit_From_Pos (Typ : Entity_Id; P : Uint) return Entity_Id
   with
     Pre  => Is_Enumeration_Type (Typ),
     Post => Nkind (Get_Enum_Lit_From_Pos'Result) in N_Identifier
                                                   | N_Character_Literal;
   --  Same as Sum_Util.Get_Enum_Lit_From_Pos except that Loc parameter is
   --  always No_Location.

   --------------------------------
   --  For Modular Integer Types --
   --------------------------------

   function Modular_Size (Typ : Entity_Id) return Uint with
     Pre => Is_Modular_Integer_Type (Typ);
   --  Out of 8, 16, 32, 64 and 128, return the smallest X such that 2 ** X is
   --  greater or equal to the modulus of the type. This is basically used to
   --  determine the bitvector used for proof. Note that this can be different
   --  from the Ada RM Size of the type, which can be changed via a Size
   --  declaration.

   function Modulus (Typ : Entity_Id) return Uint with
     Pre => Is_Modular_Integer_Type (Typ);
   --  Same as Einfo.Modulus except that it goes to the Base_Retysp

   function Non_Binary_Modulus (Typ : Entity_Id) return Boolean with
     Pre => Is_Modular_Integer_Type (Typ);
   --  Same as Einfo.Non_Binary_Modulus except that it goes to the Base_Retysp

   ----------------------------
   --  For Fixed Point Types --
   ----------------------------

   function Small_Value (Typ : Entity_Id) return Ureal with
     Pre => Is_Fixed_Point_Type (Typ);

   ------------------
   --  For Records --
   ------------------

   function Discriminant_Constraint (Typ : Entity_Id) return Elist_Id with
     Pre  => Is_Type (Typ) and then Has_Discriminants (Typ);

   function Has_Defaulted_Discriminants (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);

   function Has_Discriminants (Typ : Entity_Id) return Boolean with
     Pre => Is_Type (Typ);
   --  Same as Einfo.Has_Discriminants except that it ignores completely
   --  hidden discriminants.

   function First_Discriminant (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Type (Typ) and then Has_Discriminants (Typ),
     Post => Ekind (First_Discriminant'Result) = E_Discriminant
     and then
       SPARK_Util.Is_Not_Hidden_Discriminant (First_Discriminant'Result);
   --  Same as Sem_Aux.First_Discriminants except that it ignores completely
   --  hidden discriminants.

   procedure Next_Discriminant (Discr : in out Entity_Id) with
     Pre  => Ekind (Discr) = E_Discriminant,
     Post => (if Present (Discr) then
                  Ekind (Discr) = E_Discriminant
                  and then SPARK_Util.Is_Not_Hidden_Discriminant (Discr));
   --  Same as Einfo.Next_Discriminants except that it ignores completely
   --  hidden discriminants.

   function Stored_Constraint (Typ : Entity_Id) return Elist_Id with
     Pre  => Ekind (Typ) in Record_Kind
                          | Concurrent_Kind
                          | Private_Kind;

   --------------------------
   --  For Protected Types --
   --------------------------

   function Has_Attach_Handler (Typ : Entity_Id) return Boolean with
     Pre => Ekind (Typ) = E_Protected_Type;

   function Has_Interrupt_Handler (Typ : Entity_Id) return Boolean with
     Pre => Ekind (Typ) = E_Protected_Type;

   -----------------
   --  For Arrays --
   -----------------

   function Component_Type (Typ : Entity_Id) return Entity_Id with
     Pre  => Is_Array_Type (Typ),
     Post => Is_Type (Component_Type'Result);

   function Default_Aspect_Component_Value (Typ : Entity_Id) return Node_Id
   with Pre  => Is_Array_Type (Typ);
   --  Same as Einfo.Default_Aspect_Component_Value except that it goes to the
   --  Base_Retysp.

   function First_Index (Typ : Entity_Id) return Node_Id with
     Pre => Is_Array_Type (Typ);

   procedure Next_Index (Index : in out Node_Id) renames Einfo.Next_Index;

   function Next_Index (Index : Node_Id) return Node_Id
    renames Einfo.Next_Index;

   function Number_Dimensions (Typ : Entity_Id) return Pos with
     Pre => Ekind (Typ) in Array_Kind | E_String_Literal_Subtype;

   ------------------
   --  For Strings --
   ------------------

   function String_Literal_Length (Typ : Entity_Id) return Uint with
     Pre => Ekind (Typ) = E_String_Literal_Subtype;

   function String_Literal_Low_Bound (Typ : Entity_Id) return Node_Id with
     Pre => Ekind (Typ) = E_String_Literal_Subtype;

   -----------------------
   --  For Access Types --
   -----------------------

   function Designates_Incomplete_Type (E : Entity_Id) return Boolean with
     Pre => Is_Access_Type (E);
   --  Returns True if E is an access type which designates an incomplete type
   --  or a partial view of a type.

   function Directly_Designated_Type (E : Entity_Id) return Node_Id with
     Pre => Is_Access_Type (E);
   --  If E designates an incomplete type, return its full view, else return
   --  the designated type.

   function Can_Never_Be_Null (E : Entity_Id) return Boolean renames
     Einfo.Can_Never_Be_Null;

   function Is_Access_Constant (E : Entity_Id) return Boolean renames
     Einfo.Is_Access_Constant;

   function Access_Subprogram_Wrapper (E : Entity_Id) return Entity_Id renames
     Einfo.Access_Subprogram_Wrapper;

   ------------------
   --  For Objects --
   ------------------

   function Actual_Subtype (Obj : Entity_Id) return Entity_Id with
     Pre  => Ekind (Obj) in E_Constant | E_Variable or else Is_Formal (Obj),
     Post =>
       (if Present (Actual_Subtype'Result) then
              Is_Type (Actual_Subtype'Result));

   function Component_Clause (Obj : Entity_Id) return Node_Id with
     Pre => Ekind (Obj) in E_Discriminant | E_Component;

   function Component_First_Bit (Obj : Entity_Id) return Uint with
     Pre => Ekind (Obj) in E_Discriminant | E_Component
     and then Known_Component_First_Bit (Obj);
   --  Returns the first bit of a component if it has been supplied

   function Component_Last_Bit (Obj : Entity_Id) return Uint with
     Pre => Ekind (Obj) in E_Discriminant | E_Component
     and then Known_Component_Last_Bit (Obj);
   --  Returns the last bit of a component if it has been supplied

   function Component_Position (Obj : Entity_Id) return Uint with
     Pre => Ekind (Obj) in E_Discriminant | E_Component
     and then Present (Component_Clause (Obj));
   --  Returns the position of a component if it has been supplied

   function Constant_Value (Obj : Entity_Id) return Node_Id with
     Pre => Ekind (Obj) = E_Constant;

   function Discriminal_Link (Obj : Entity_Id) return Node_Id with
     Pre  => Is_Discriminal (Obj),
     Post => Ekind (Discriminal_Link'Result) = E_Discriminant;

   function Discriminant_Default_Value (Obj : Entity_Id) return Node_Id with
     Pre => Ekind (Obj) = E_Discriminant;

   function Enclosing_Type (Obj : Entity_Id) return Node_Id with
     Pre  => Ekind (Obj) in
       E_Discriminant | E_Component | E_Constant | E_In_Parameter
     or else Sem_Aux.Is_Protected_Operation (Obj),
     Post => Is_Type (Enclosing_Type'Result)
       and then Ekind (Enclosing_Type'Result) in
       Record_Kind | Private_Kind | Concurrent_Kind;
   --  Return the scope of a record component, discriminant, discriminal or
   --  protected operation.

   function Enumeration_Pos (Obj : Entity_Id) return Uint with
     Pre => Ekind (Obj) = E_Enumeration_Literal;

   function Enumeration_Rep (Obj : Entity_Id) return Uint with
     Pre => Ekind (Obj) = E_Enumeration_Literal;

   function Full_View (Obj : Entity_Id) return Entity_Id with
     Pre  => Ekind (Obj) = E_Constant
       and then SPARK_Util.Is_Partial_View (Obj),
     Post => Ekind (Full_View'Result) = E_Constant;

   function Known_Component_First_Bit (Obj : Entity_Id) return Boolean with
     Pre => Ekind (Obj) in E_Discriminant | E_Component;
   --  Returns True if the first bit of a component has been supplied either
   --  through a component clause or directly.

   function Known_Component_Last_Bit (Obj : Entity_Id) return Boolean with
     Pre => Ekind (Obj) in E_Discriminant | E_Component;
   --  Returns True if the last bit of a component has been supplied either
   --  through a component clause or through appropriate offset and component
   --  size.

   ----------------------
   --  For Subprograms --
   ----------------------

   function First_Formal (Subp : Entity_Id) return Entity_Id with
     Pre  => Ekind (Subp) in Einfo.Generic_Subprogram_Kind
                           | Einfo.Overloadable_Kind
                           | Einfo.E_Entry_Family
                           | Einfo.E_Subprogram_Body
                           | Einfo.E_Subprogram_Type,
     Post => (if Present (First_Formal'Result) then
                  Einfo.Is_Formal (First_Formal'Result));
   --  Same as Einfo.First_Formal except that it ignores the formal introduced
   --  for the access-to-subprogram object in access subprogram wrappers.

   function Number_Formals (Subp : Entity_Id) return Natural with
     Pre  => Ekind (Subp) in Einfo.Generic_Subprogram_Kind
                           | Einfo.Overloadable_Kind
                           | Einfo.E_Entry_Family
                           | Einfo.E_Subprogram_Body
                           | Einfo.E_Subprogram_Type;
   --  Same as Einfo.Number_Formals except that it ignores the formal
   --  introduced for the access-to-subprogram object in access subprogram
   --  wrappers.

   function Has_Controlling_Result (Subp : Entity_Id) return Boolean with
     Pre => Ekind (Subp) = E_Function;

   function Has_Pragma_Volatile_Function (Subp : Entity_Id) return Boolean with
     Pre  => Ekind (Subp) in Einfo.Subprogram_Kind
                           | Einfo.E_Subprogram_Type;
   --  Return True if Subp has a pragma Volatile_Function or if it is an
   --  unchecked conversion with a volatile profile.
   --  This is different from Sem_Util.Is_Volatile_Function as it does not
   --  return True of protected functions.

   function Is_Expression_Function_Or_Completion
     (Subp : Entity_Id)
      return Boolean
   with Pre =>
       Ekind (Subp) in Einfo.Subprogram_Kind | Einfo.E_Subprogram_Type;

   function Is_Predicate_Function (Subp : Entity_Id) return Boolean with
     Pre => Einfo.Is_Subprogram (Subp);

   function Is_Visible_Dispatching_Operation (Subp : Entity_Id) return Boolean;
   --  Return True if Subp is a dispatching operation and there is a visibly
   --  tagged dispatching type (SPARK_Util.Subprograms.Find_Dispatching_Type
   --  returns True).

   function Next_Formal (Formal : Entity_Id) return Entity_Id with
     Pre  => Einfo.Is_Formal (Formal),
     Post => No (Next_Formal'Result)
       or else Einfo.Is_Formal (Next_Formal'Result);
   --  Same as Einfo.Next_Formal except that it ignores the formal introduced
   --  for the access-to-subprogram object in access subprogram wrappers.

   procedure Next_Formal (Formal : in out Entity_Id) with
     Pre  => Einfo.Is_Formal (Formal),
     Post => No (Formal) or else Einfo.Is_Formal (Formal);
   --  Same as Einfo.Next_Formal except that it ignores the formal introduced
   --  for the access-to-subprogram object in access subprogram wrappers.

   function No_Return (Subp : Entity_Id) return Boolean renames
     Einfo.No_Return;

   function Null_Present (Subp : Entity_Id) return Boolean with
     Pre => Ekind (Subp) = E_Procedure;
   --  Applies Sinfo.Null_Present on the specification of Subp.

   function Subprogram_Specification (Subp : Entity_Id) return Node_Id with
     Pre  => Ekind (Subp) in Subprogram_Kind | E_Entry,
     Post => Nkind (Subprogram_Specification'Result) in
         N_Function_Specification
       | N_Procedure_Specification
       | N_Entry_Declaration;
   --  Same as Sem_Aux.Subprogram_Specification except that it also works on
   --  entries.

   function Is_Unchecked_Conversion_Instance (Subp : Entity_Id) return Boolean
   with Pre => Ekind (Subp) in Subprogram_Kind | E_Entry | E_Subprogram_Type;
   --  Same as Sem_Util.Is_Unchecked_Conversion_Instance

   -------------------
   --  For Packages --
   -------------------

   function Is_Wrapper_Package (Pack : Entity_Id) return Boolean with
     Pre => Ekind (Pack) = E_Package;

   function Package_Body (Pack : Entity_Id) return Node_Id with
     Pre => Ekind (Pack) = E_Package;

   function Package_Body_Entity (Pack : Node_Id) return Entity_Id with
     Pre => Nkind (Pack) = N_Package_Body;

   function Package_Spec (Pack : Entity_Id) return Node_Id with
     Pre => Ekind (Pack) = E_Package;

   function Private_Declarations_Of_Package (Pack : Entity_Id) return List_Id
   with
     Pre => Ekind (Pack) = E_Package;
   --  @param E a package entity
   --  @return the list of private declarations of the package

   function Visible_Declarations_Of_Package (Pack : Entity_Id) return List_Id
   with
     Pre => Ekind (Pack) = E_Package;
   --  @param E a package entity
   --  @return the list of visible declarations of the package

   -------------------------
   --  For other entities --
   -------------------------

   function Alignment (Ent : Entity_Id) return Uint with
     Pre => (Is_Type (Ent) or else Is_Object (Ent))
       and then Known_Alignment (Ent);

   function Enclosing_Declaration (E : Entity_Id) return Node_Id with
     Pre  => Is_Object (E) or else Is_Named_Number (E) or else Is_Type (E),
     Post => Nkind (Enclosing_Declaration'Result) in
         Sinfo.N_Declaration
       | Sinfo.N_Later_Decl_Item
       | Sinfo.N_Number_Declaration;
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

   function Return_Applies_To (E : Entity_Id) return Node_Id with
     Pre => Ekind (E) = Einfo.E_Return_Statement;

end SPARK_Atree.Entities;
