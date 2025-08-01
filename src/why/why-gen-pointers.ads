------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - P O I N T E R S                     --
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

with Gnat2Why.Util;          use Gnat2Why.Util;
with SPARK_Atree;            use SPARK_Atree;
with SPARK_Atree.Entities;   use SPARK_Atree.Entities;
with SPARK_Definition;       use SPARK_Definition;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Util.Types;       use SPARK_Util.Types;
with Types;                  use Types;
with Why.Gen.Binders;        use Why.Gen.Binders;
with Why.Ids;                use Why.Ids;
with Why.Conversions;        use Why.Conversions;
with Why.Sinfo;              use Why.Sinfo;

package Why.Gen.Pointers is
   --  This package encapsulates the encoding of access types into Why.

   procedure Declare_Rep_Pointer_Compl_If_Needed (E : Entity_Id)
   with Pre => Is_Access_Type (E) and then Designates_Incomplete_Type (E);
   --  Declare a new module for completion of access types designating
   --  incomplete types if there isn't one already.

   procedure Declare_Ada_Pointer (Th : Theory_UC; E : Entity_Id)
   with Pre => Is_Access_Type (E);
   --  Emit all necessary Why3 declarations to support Ada pointers.
   --  @param P the Why section to insert the declaration
   --  @param E the type entity to translate

   procedure Create_Rep_Pointer_Theory_If_Needed (E : Entity_Id);
   --  Similar to Create_Rep_Record_Theory_If_Needed but handles objects of
   --  access type. It declares a pointer type as a why record with three
   --  fields: pointer_value, is_null_pointer, and is_moved.
   --  It also defines the needed functions to manipulate this type.

   procedure Create_Move_Tree_Theory_For_Pointer
     (Th : Theory_UC; E : Entity_Id)
   with
     Pre =>
       Is_Access_Type (E)
       and then Contains_Allocated_Parts (E)
       and then not Is_Anonymous_Access_Type (E);
   --  Create a module declaring a type for the move trees for objects of type
   --  E.

   procedure Create_Move_Tree_For_Incomplete_Access (E : Entity_Id)
   with Pre => Has_Incomplete_Access (E) and then Contains_Allocated_Parts (E);
   --  Declare abstract move tree for a type with an incomplete access

   procedure Complete_Move_Tree_For_Incomplete_Access
     (Th : Theory_UC; E : Entity_Id)
   with Pre => Has_Incomplete_Access (E) and then Contains_Allocated_Parts (E);
   --  Complete the abstract move tree for a type with an incomplete access

   procedure Declare_Init_Wrapper_For_Pointer (Th : Theory_UC; E : Entity_Id)
   with Pre => Is_Access_Type (E) and then Has_Init_Wrapper (E);

   function New_Move_Tree_Pointer_Value_Access
     (Ty : Entity_Id; Name : W_Expr_Id; Domain : EW_Domain) return W_Expr_Id
   with Pre => Contains_Allocated_Parts (Directly_Designated_Type (Ty));
   --  Access to the move tree of the designated value

   function New_Move_Tree_Pointer_Value_Update
     (Ty : Entity_Id; Name : W_Prog_Id; Value : W_Prog_Id) return W_Prog_Id
   with Pre => Contains_Allocated_Parts (Directly_Designated_Type (Ty));
   --  Update to the move tree of the designated value

   function Has_Predeclared_Init_Predicate (E : Entity_Id) return Boolean
   with Pre => Is_Type (E) and then Has_Init_Wrapper (E);
   --  Return True if the is_initialized predicate needs to be declared
   --  separately from its definition to avoid circularity (E is the completion
   --  of an incomplete type designated by an access type with an
   --  initialization wrapper).

   function New_Ada_Pointer_Update
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id) return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to the update to an Ada
   --  pointer (the pointed value). Emit all necessary checks.
   --  Note that this function does not generate an assignment, instead it
   --  returns a functional update. It will look like
   --    { name with Pointer_Value = value }
   --  The assignment, if required, needs to be generated by the caller.

   function New_Pointer_Is_Null_Access
     (E : Entity_Id; Name : W_Expr_Id; Local : Boolean := False)
      return W_Expr_Id;
   --  Return an access to the Is_Null field of the pointer why record.
   --  @param E the Ada type entity
   --  @param Name name of the pointer to access
   --  @param Local whether we want the local or the global access

   function New_Pointer_Is_Null_Access
     (E : Entity_Id; Name : W_Prog_Id; Local : Boolean := False)
      return W_Prog_Id
   is (+W_Expr_Id'(New_Pointer_Is_Null_Access (E, +Name, Local)));

   function New_Pointer_Is_Null_Access
     (E : Entity_Id; Name : W_Term_Id; Local : Boolean := False)
      return W_Term_Id
   is (+W_Expr_Id'(New_Pointer_Is_Null_Access (E, +Name, Local)));

   function New_Pointer_Value_Access
     (Ada_Node : Node_Id := Empty;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain;
      Local    : Boolean := False) return W_Expr_Id;
   --  Return an access to the Pointer_Value field of the pointer why record.
   --  @param E the Ada type entity
   --  @param Name name of the pointer to access
   --  @param Local whether we want the local or the global access

   function New_Pointer_Value_Access
     (Ada_Node : Node_Id := Empty;
      E        : Entity_Id;
      Name     : W_Term_Id;
      Local    : Boolean := False) return W_Term_Id
   is (+W_Expr_Id'
         (New_Pointer_Value_Access (Ada_Node, E, +Name, EW_Term, Local)));

   function Repr_Pointer_Type (E : Entity_Id) return Entity_Id
   with Pre => Has_Access_Type (E);
   --  Return the first pointer type defined with the same designated type.

   function Root_Pointer_Type (E : Entity_Id) return Entity_Id
   with Pre => Has_Access_Type (E);
   --  Return the representative of the root of E

   function Pointer_From_Split_Form
     (I : Item_Type; Ref_Allowed : Boolean) return W_Term_Id
   with Pre => I.Kind = Pointer;
   --  Reconstructs a complete pointer from an item in split form.

   function Pointer_From_Split_Form
     (Ada_Node     : Node_Id := Empty;
      A            : W_Expr_Array;
      Ty           : Entity_Id;
      Local        : Boolean := False;
      Relaxed_Init : Boolean := False;
      Force_Dummy  : Boolean := False) return W_Term_Id;
   --  Reconstructs a complete pointer of type Ty from an array of expressions
   --  representing a split form. A should contain first the value, then
   --  is_null and the initialization flag if Relaxed_Init is True. If
   --  Force_Dummy is True, explicitly set the value field to dummy when the
   --  pointer is null. It is useful for conversion functions to create valid
   --  values with different dummy constants.

   function Prepare_Args_For_Access_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id;
      Domain   : EW_Domain;
      Params   : Transformation_Params) return W_Expr_Array;
   --  Given a pointer type, compute the argument array that can be used
   --  together with its subtype check predicate of program function. The
   --  last argument is actually the given expression itself.

   function Insert_Pointer_Subtype_Check
     (Ada_Node : Node_Id; Check_Ty : Entity_Id; Expr : W_Prog_Id)
      return W_Prog_Id;
   --  Insert a check that an expression is in the range of a pointer subtype
   --  @param Ada_Node used to locate the check
   --  @param Check_Ty pointer type
   --  @param Expr why expression. Expr should be of type
   --     EW_Abstract (Root_Pointer_Type (Check_Ty))

   ---------------
   -- Borrowers --
   ---------------

   procedure Declare_At_End_Function
     (File : Theory_UC; E : Entity_Id; Binders : Binder_Array)
   with Pre => Is_Borrowing_Traversal_Function (E);
   --  Emit a function computing the value at the end of the borrow of the
   --  borrowed parameter from the value of the end of the borrow of the result
   --  of the borrowing traversal function E.

   procedure Declare_At_End_Ref (Th : Theory_UC; E : Entity_Id)
   with Pre => Is_Local_Borrower (E);
   --  Emit a global reference for the value at the end of a local borrower E.
   --  Also declare a global constant for the value of the borrowed expression
   --  at the end of the borrow.

   function Get_Borrowed_At_End (E : Entity_Id) return W_Identifier_Id
   with
     Pre => Is_Local_Borrower (E) or else Is_Borrowing_Traversal_Function (E);
   --  Get the identifier introduced for the value of the borrowed expression
   --  at the end of the borrow. It is a constant.

   function Get_Borrowed_Entity (E : Entity_Id) return Entity_Id
   with
     Pre => Is_Local_Borrower (E) or else Is_Borrowing_Traversal_Function (E);
   --  Get the borrowed entity

   function Get_Borrowed_Expr (E : Entity_Id) return Node_Id
   with
     Pre  => Is_Local_Borrower (E),
     Post => Nkind (Get_Borrowed_Expr'Result) in N_Subexpr;
   --  Get the initial borrowed expression

   function Get_Borrowed_Typ (E : Entity_Id) return Entity_Id
   with
     Pre  => Is_Local_Borrower (E) or else Is_Borrowing_Traversal_Function (E),
     Post => Is_Type (Get_Borrowed_Typ'Result);
   --  Get the type of the borrower of initially borrowed expression

   function Get_Brower_At_End (E : Entity_Id) return W_Identifier_Id
   with
     Pre => Is_Local_Borrower (E) or else Is_Borrowing_Traversal_Function (E);
   --  Get the identifier introduces for the value of the borrower at the end
   --  of the borrow. It is a reference to handle reborrows, except in the
   --  postcondition of traversal functions.

end Why.Gen.Pointers;
