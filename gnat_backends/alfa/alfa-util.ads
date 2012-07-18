------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             A L F A . U T I L                            --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012, AdaCore                       --
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

with Atree; use Atree;
with Einfo; use Einfo;
with Sinfo; use Sinfo;

package Alfa.Util is

   function Lowercase_Has_Element_Name return String;
   --  Return the name of the function Has_Element in formal containers

   function Lowercase_Iterate_Name return String;
   --  Return the name of the function Iterate in formal containers

   function Lowercase_Capacity_Name return String;
   --  Return the name of the discriminant Capacity in formal containers

   function Aggregate_Is_Fully_Initialized (N : Node_Id) return Boolean;
   --  Return whether aggregate N is fully initialized

   function All_Aggregates_Are_Fully_Initialized
     (N : Node_Id) return Boolean;
   --  Return whether all aggregates in node N (recursively) are fully
   --  initialized.

   function Get_Enclosing_Declaration (N : Node_Id) return Node_Id;
   --  Return the declaration node enclosing N, if any, by following the chain
   --  of Parent's links.

   function Get_Expression_Function (E : Entity_Id) return Node_Id;
   --  If E is the entity of an expression function, return the corresponding
   --  N_Expression_Function original node. Otherwise, return Empty.

   function Get_Subprogram_Body (E : Entity_Id) return Node_Id;
   --  Return the N_Subprogram_Body node for a subprogram entity E

   function Get_Subprogram_Spec (E : Entity_Id) return Node_Id;
   --  Return the N_Specification node for a subprogram entity E

   function Expression_Functions_All_The_Way (E : Entity_Id) return Boolean;
   --  Given the entity E for a function, determine whether E is an expression
   --  function that only calls expression functions, directly or indirectly.

   procedure Add_Full_And_Partial_View (Full, Partial : Entity_Id);
   --  Store the correspondance between the Full and Partial views of the same
   --  entity, for deferred constants and private types.

   function Is_Full_View (E : Entity_Id) return Boolean;
   --  Return whether E is the full view of another entity

   function Is_Formal_Container_Capacity (E : Entity_Id) return Boolean
   with
     Pre => Ekind (E) = E_Discriminant;

   function Is_Access_To_Formal_Container_Capacity (N : Node_Id) return Boolean
   with
     Pre => Nkind (N) = N_Selected_Component;

   function Is_Instantiation_Of_Formal_Container (N : Node_Id) return Boolean;
   --  Return whether N is the package instantiation of a formal container

   function Partial_View (E : Entity_Id) return Entity_Id;
   --  Return the partial view for entity E

   function Most_Underlying_Type (E : Entity_Id) return Entity_Id;
   --  Takes a type E in parameter. If E is a private type or a record subtype,
   --  follow the chain of underlying types (for a private type) and base types
   --  (for a record subtype) to return the first non-private type which is not
   --  also a record subtype. Otherwise, return E.

   function Location_In_Formal_Containers (Loc : Source_Ptr) return Boolean;
   --  Return whether a location Loc is in the formal container sources

   function Type_In_Container (Id : Entity_Id) return Boolean;
   --  Return whether a type Id is in the formal container sources

end Alfa.Util;
