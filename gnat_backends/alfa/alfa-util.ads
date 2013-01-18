------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             A L F A . U T I L                            --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
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

with Atree;            use Atree;
with Debug;
with Einfo;            use Einfo;
with Impunit;          use Impunit;
with Namet;            use Namet;
with Sinfo;            use Sinfo;
with Snames;           use Snames;

with Why.Atree.Tables; use Why.Atree.Tables;

with Gnat2Why.Nodes;   use Gnat2Why.Nodes;

package Alfa.Util is

   -------------------
   -- Special modes --
   -------------------

   --  These modes are currently set through debug flags

   function Translate_Standard_Only return Boolean is
     (Debug.Debug_Flag_Dot_HH);

   function In_Detect_Mode_Only return Boolean is (Debug.Debug_Flag_Dot_KK);

   function In_Check_Mode_Only return Boolean is (Debug.Debug_Flag_Dot_GG);

   ---------------
   -- Utilities --
   ---------------

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
   --  Takes a type E in parameter. If E is a private type, follow the chain of
   --  underlying types to return the first non-private type. Otherwise, return
   --  E. As a special case, return the first type in a formal container found.

   function Location_In_Formal_Containers (Loc : Source_Ptr) return Boolean;
   --  Return whether a location Loc is in the formal container sources

   function Unit_In_Standard_Library (U : Unit_Number_Type) return Boolean is
      (Get_Kind_Of_Unit (U) /= Not_Predefined_Unit);
   --  Returns True is unit U is in the standard library, which includes all
   --  units defined in Ada RM, and all units predefined by GNAT.

   function Location_In_Standard_Library (Loc : Source_Ptr) return Boolean;
   --  Returns True if location Loc is in a unit of the standard library, as
   --  computed by Unit_In_Standard_Library.

   function Type_Based_On_Formal_Container (E : Entity_Id) return Boolean;
   --  Return whether a type E is defined in the formal containers, or it is a
   --  subtype or derived type ultimately based on such a type.

   function Type_In_Formal_Container (Id : Entity_Id) return Boolean;
   --  Return whether a type Id is in the formal container sources

   function Entity_Is_Instance_Of_Formal_Container (Id : Entity_Id)
                                                    return Boolean;
   --  return whether the entity Id is the instance of an entity defined in the
   --  formal containers.

   function Underlying_Formal_Container_Type (E : Entity_Id) return Entity_Id;
   --  Return the underlying base type in formal containers, if any

   function Root_Record_Type (E : Entity_Id) return Entity_Id;
   --  Given a record type (or private type whose implementation is a record
   --  type, etc.), return the root type, including traversing private types.

   function Root_Record_Component (E : Entity_Id) return Entity_Id;
   --  Given a component or discriminant of a record (sub-)type, return the
   --  corresponding component or discriminant of the root type. This is the
   --  identity when E is the component of a root type.

   function Search_Component_By_Name
     (Rec  : Entity_Id;
      Comp : Entity_Id) return Entity_Id;
   --  Given a record type entity and a component/discriminant entity, search
   --  in Rec a component/discriminant entity with the same name. The caller of
   --  this function should be sure that there is such a component, because it
   --  raises Program_Error if it doesn't find any.

   function Matching_Component_Association
     (Component   : Entity_Id;
      Association : Node_Id) return Boolean;
   --  Return whether Association matches Component

   function Number_Components (Typ : Entity_Id) return Natural;
   --  Count the number of components in record type Typ

   procedure Append
     (To    : in out List_Of_Nodes.List;
      Elmts : List_Of_Nodes.List);
   --  Append all elements from list Elmts to the list To

   procedure Append
     (To    : in out Node_Lists.List;
      Elmts : Node_Lists.List);
   --  Append all elements from list Elmts to the list To

   function Get_Statement_List (Stmts : List_Id) return List_Of_Nodes.List;
   --  Given a list of statements and declarations Stmts, returns the same list
   --  seen as a container list of nodes.

   function Get_Flat_Statement_List
     (Stmts : List_Id) return List_Of_Nodes.List;
   --  Given a list of statements and declarations Stmts, returns the flattened
   --  list that includes these statements and declarations, and recursively
   --  all inner declarations and statements that appear in block statements.

   function Is_Pragma (N : Node_Id; Name : Pragma_Id) return Boolean;
   --  Returns whether N is a pragma of the given kind

   function Is_Pragma_Check (N : Node_Id; Name : Name_Id) return Boolean;
   --  Returns whether N has the form pragma Check (Name, ...)

   function Innermost_Enclosing_Loop (N : Node_Id) return Node_Id;
   --  Returns the innermost loop enclosing N, if any, and Empty otherwise

end Alfa.Util;
