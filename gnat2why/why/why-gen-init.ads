------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          W H Y - G E N - I N I T                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2018-2019, AdaCore                     --
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

with Gnat2Why.Util;            use Gnat2Why.Util;
with SPARK_Atree.Entities;     use SPARK_Atree.Entities;
with Types;                    use Types;
with Why.Conversions;          use Why.Conversions;
with Why.Ids;                  use Why.Ids;
with Why.Gen.Terms;            use Why.Gen.Terms;
with Why.Sinfo;                use Why.Sinfo;

package Why.Gen.Init is
   --  This package encapsulates the encoding of initialization by proof.

   procedure Declare_Init_Wrapper (P : W_Section_Id; E : Entity_Id) with
     Pre => Is_Type (E);
   --  Add declarations for a wrapper type for E in P

   function New_Init_Wrapper_Value_Access
     (Ada_Node    : Node_Id;
      E           : Entity_Id;
      Name        : W_Expr_Id;
      Domain      : EW_Domain;
      Ref_Allowed : Boolean := True)
      return W_Expr_Id;
   --  Access the value of an expression of a wrapper type

   function New_Init_Attribute_Access
     (E           : Entity_Id;
      Name        : W_Expr_Id;
      Ref_Allowed : Boolean := True)
      return W_Expr_Id;
   --  Access the initialization flag of an expression of a wrapper type

   function EW_Init_Wrapper (E : Entity_Id; K : EW_Type) return W_Type_Id with
     Pre => Is_Type (E) and then K in EW_Abstract | EW_Split;
   --  Wrappers can be either in abstract or in split form. If they are in
   --  abstract form, they are records with an initialization flag and a value.
   --  If they are in split form, the initialization flag should be queried
   --  from the Symbol_Table using the Ada_Node.

   function EW_Init_Wrapper (Ty : W_Type_Id) return W_Type_Id;
   --  Get ada node and kind from existing type

   function Is_Init_Wrapper_Type (Typ : W_Type_Id) return Boolean;
   --  True is a type is a wrapper type

   function Reconstruct_Init_Wrapper
     (Ada_Node  : Node_Id := Empty;
      Ty        : Entity_Id;
      Value     : W_Expr_Id;
      Init_Attr : W_Expr_Id := +True_Term)
      return W_Expr_Id;
   --  From a value of type EW_Abstract (Ty), reconstruct the corresponding
   --  wrapper if any.

   function Compute_Is_Initialized
     (E           : Entity_Id;
      Name        : W_Term_Id;
      Ref_Allowed : Boolean)
      return W_Pred_Id;
   --  Whether Name is initialized. This does not only include the top level
   --  initialization flag of E but also the flags of nested components for
   --  composite types.

   function Insert_Initialization_Check
     (Ada_Node : Node_Id;
      E        : Entity_Id;
      Name     : W_Expr_Id;
      Domain   : EW_Domain)
      return W_Expr_Id;
   --  If Domain = EW_Prog, insert a check that Name is initialized

end Why.Gen.Init;
