------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - I N I T                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2025, AdaCore                     --
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

with Gnat2Why.Util;        use Gnat2Why.Util;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Modules;    use Why.Atree.Modules;
with Why.Conversions;      use Why.Conversions;
with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;

package Why.Gen.Init is
   --  This package encapsulates the encoding of initialization by proof.

   procedure Declare_Simple_Wrapper_Type
     (Th           : Theory_UC;
      W_Nam        : W_Name_Id;
      Init_Val     : W_Identifier_Id;
      Attr_Init    : W_Identifier_Id;
      Of_Wrapper   : W_Identifier_Id;
      To_Wrapper   : W_Identifier_Id;
      Dummy        : W_Identifier_Id;
      Default_Init : Boolean);
   --  Declare a wrapper type with name W_Nam, and fields Init_Val and
   --  Attr_Init. Also generate conversion functions with names
   --  Of_Wrapper and To_Wrapper, as well as an initialized object with
   --  name Dummy. Dummy is initialized iff Default_Init is True.

   procedure Declare_Init_Wrapper (Th : Theory_UC; E : Entity_Id)
   with Pre => Is_Type (E);
   --  Add declarations for a wrapper type for E in P

   function Is_Init_Wrapper_Type (Typ : W_Type_Id) return Boolean;

   function EW_Init_Wrapper (Ty : W_Type_Id) return W_Type_Id
   with
     Pre =>
       Ty = EW_Bool_Type
       or else
         (Get_Type_Kind (Ty) in EW_Abstract | EW_Split
          and then Has_Init_Wrapper (Get_Ada_Node (+Ty)));
   --  Return the init wrapper type with the same Ada node and kind as Ty

   type Exclude_Components_Kind is (For_Eq, Relaxed, None);

   function Compute_Is_Initialized
     (E                  : Entity_Id;
      Name               : W_Expr_Id;
      Params             : Transformation_Params;
      Domain             : EW_Domain;
      Exclude_Components : Exclude_Components_Kind;
      No_Predicate_Check : Boolean := False;
      Use_Pred           : Boolean := True) return W_Expr_Id
   with
     Pre =>
       (if Present (E) and then Contains_Access_Subcomponents (E)
        then Exclude_Components /= None);
   --  If Exclude_Components is None, the predicate symbol cannot be
   --  used and the function will loop on recursive data-structures.

   --  Whether Name is initialized. This does not only include the top level
   --  initialization flag of Name but also the flags of nested components for
   --  composite types. E should be the Ada type of Name unless Name is a
   --  standard boolean.
   --
   --  If Exclude_Components is Relaxed, do not include initialization of
   --  subcomponents whose type is annotated with relaxed initialization. A
   --  part of an expression which has relaxed initialization may not be of a
   --  type with comes from an object which has relaxed initialization, or if
   --  it is a relaxed initialization, for example, if it part of a composite
   --  expression which itself has a type with relaxed initialization. Some
   --  initialization checks are only interested with these parts which do not
   --  have a type with relaxed initialization. This happens for example when
   --  storing the expression in an object of its type, or when giving it as a
   --  parameter to a function call.
   --
   --  If Exclude_Components is For_Eq, relaxed (strict) subcomponents of
   --  (strict) subcomponents of Name whose type has a user-defined equality
   --  will be excluded.
   --
   --  For init wrappers of composite types, Is_Initialized will include a
   --  predicate check if any. If No_Predicate_Check is True, then the
   --  predicate of the type itself will not be included. Predicates of
   --  subcomponents are still considered.
   --
   --  If Use_Pred is True, use the predicate symbol introduced for the type
   --  whenever possible.

   function New_Init_Attribute_Access
     (E : Entity_Id; Name : W_Term_Id) return W_Term_Id;
   --  Access the initialization flag of an expression of a wrapper type.
   --  Name shall be of the init wrapper type of Boolean or E shall be a type
   --  entity which has a wrapper (simple private type, type with mutable
   --  discriminants, or scalar type).

   function Insert_Initialization_Check
     (Ada_Node           : Node_Id;
      E                  : Entity_Id;
      Name               : W_Expr_Id;
      Domain             : EW_Domain;
      Exclude_Components : Exclude_Components_Kind;
      No_Predicate_Check : Boolean := False) return W_Expr_Id;
   --  If Domain = EW_Prog, insert a check that Name is initialized

   function Insert_Top_Level_Init_Check
     (Ada_Node : Node_Id;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain;
      Do_Check : Boolean := True;
      Details  : String := "") return W_Expr_Id;
   --  If Domain = EW_Prog, insert a check that the mutable discriminants or
   --  pointer address of Name (if any) are initialized.
   --  Details is used to generate the check details (aka reason for check).

end Why.Gen.Init;
