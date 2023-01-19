------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--           G N A T 2 W H Y - S U B P R O G R A M S - P O I N T E R S      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2020-2023, AdaCore                     --
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

with Namet;                           use Namet;
with Snames;                          use Snames;
with Why.Types;                       use Why.Types;

package Gnat2Why.Subprograms.Pointers is

   procedure Declare_Access_To_Subprogram_Type
     (Th : Theory_UC;
      E  : Access_Kind_Id)
   with
     Pre => Is_Access_Subprogram_Type (E);
   --  Declare a theory for an access to subprogram type by exporting the
   --  M_Subprogram_Access module. Also declare a specific range predicate
   --  which can be used to express that an access to subprogram object
   --  belongs to the specific access to subprogram type.

   procedure Complete_Access_To_Subprogram_Type
     (Th : Theory_UC;
      E  : Access_Kind_Id)
   with
     Pre => Is_Access_Subprogram_Type (E);
   --  Declare a program function __call_ with appropriate contracts to call
   --  objects of type E in the program domain. For functions, also generate an
   --  axiom supplying the definition of the range predicate of E.

   procedure Create_Theory_For_Profile_If_Needed (E : Access_Kind_Id)
   with
     Pre => Is_Access_Subprogram_Type (E);
   --  Create a theory for a profile E if no theory has been declared for the
   --  same profile. For function profiles, this theory contains a logic __call
   --  function which is shared between all access to subprogram types which
   --  have the same profile.

   function New_Dynamic_Property_For_Subprogram
     (Ty     : Access_Kind_Id;
      Expr   : W_Term_Id;
      Params : Transformation_Params)
      return W_Pred_Id
   with
     Pre => Is_Access_Subprogram_Type (Ty);
   --  Compute the dynamic property of an access to subprogram expression. It
   --  calls the range predicate defined in the module for the subprogram type.
   --  For functions, this predicate supplies the contract of the access to
   --  subprogram type on the logic __call function.

   function New_Subprogram_Value_Access
     (Ada_Node : Entity_Id := Empty;
      Expr     : W_Expr_Id;
      Domain   : EW_Domain)
      return W_Expr_Id;
   --  Access the subprogram object designated by a subprogram access Expr. If
   --  Domain is EW_Prog, also perform dereference checks.

   function Checks_For_Subp_Conversion
     (Ada_Node : Entity_Id;
      Expr     : W_Expr_Id := Why_Empty;
      From, To : Entity_Id;
      Params   : Transformation_Params)
      return W_Prog_Id
   with
     Pre => Is_Access_Subprogram_Type (To)
       and then (Is_Subprogram (From)
                  or else Is_Access_Subprogram_Type (From))
       and then (Is_Subprogram (From) or else Expr /= Why_Empty);
   --  Perform LSP checks to ensure that contracts of To are compatible with
   --  contracts of From. Expr is the Why expression for the subprogram
   --  access. It is used to have a precise knowledge of the converted
   --  subprogram for functions.
   --  These checks are meant to be inlined at the point of conversion, as
   --  opposed to generated in a separate module like LSP checks for
   --  tagged type.

   function Transform_Access_Attribute_Of_Subprogram
     (Expr   : N_Attribute_Reference_Id;
      Domain : EW_Domain;
      Params : Transformation_Params)
      return W_Expr_Id
   with
     Pre => Attribute_Name (Expr) = Name_Access
       and then Is_Access_Subprogram_Type (Etype (Expr));
   --  Transform a reference to the 'Access attribute whose prefix in a
   --  subprogram name. A theory is introduced for accesses to a given
   --  subprogram so that it can be shared between occurrences.
   --  If Domain is EW_Prog, also perform LSP checks and possibly checks for
   --  specific type constraints of Etype (Expr).

   procedure Create_Theory_For_HO_Specialization_If_Needed (Call : Node_Id);
   --  Create a theory for a call to a function annotated with higher order
   --  specialization if no theory has been declared for the same
   --  specialization.

   function Get_Specialized_Function_Theory_Name
     (Call : Node_Id) return Symbol;
   --  Get the theory name for a function call with higher order specialization

   function Get_Globals_From_Specialized_Parameters
     (Params : Node_Maps.Map) return Flow_Types.Flow_Id_Sets.Set;
   --  Get the set of globals read from actual entities in the map of
   --  specialized parameters Params.

end Gnat2Why.Subprograms.Pointers;
