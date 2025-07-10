------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W _ U T I L I T Y . P R O O F _ D E P E N D E N C I E S       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2024-2025, AdaCore                     --
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
------------------------------------------------------------------------------

--  This package contains utilities related to proof dependencies.

with Flow_Classwide;
with SPARK_Util.Types; use SPARK_Util.Types;

with Namet; use Namet;

package Flow_Utility.Proof_Dependencies is

   procedure Process_Access_To_Subprogram_Contracts
     (Typ                : Type_Kind_Id;
      Scop               : Flow_Scope;
      Proof_Dependencies : in out Node_Sets.Set;
      Generating_Globals : Boolean)
   with
     Pre  => Is_Access_Subprogram_Type (Typ) and then No (Parent_Retysp (Typ)),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies by analyzing the Pre and Post contracts from
   --  an access-to-subprogram type definition.

   procedure Process_Access_Attribute
     (N : Node_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  =>
       Nkind (N) in N_Attribute_Reference
       and then Attribute_Name (N) = Name_Access,
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies when the 'Access attribute references a
   --  subprogram.

   procedure Process_Dispatching_Call
     (N : Node_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Flow_Classwide.Is_Dispatching_Call (N),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies with all possible callees for dispatching
   --  call N.

   procedure Process_Indirect_Dispatching_Equality
     (Ty : Node_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies with all potential candidates for a dispatching
   --  call on the equality of Ty.

   procedure Process_Iterable_For_Proof_Annotation
     (N : Node_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Nkind (N) in N_Iterator_Specification,
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies by analyzing the potential Iterable_For_Proof
   --  annotations associated to N.

   procedure Process_Type_Contracts
     (Typ                : Type_Kind_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Node_Sets.Set)
   with
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies by analyzing predicate and invariant expressions
   --  that apply to Typ. This also pulls contracts in access-to-subprograms
   --  types. Include_Invariant is used to determine whether a type invariant
   --  is pulled.

   procedure Process_Reclamation_Functions
     (Typ : Type_Kind_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies with the reclamation functions associated to
   --  all components of Typ.

end Flow_Utility.Proof_Dependencies;
