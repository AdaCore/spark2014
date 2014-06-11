------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Types;                              use Types;
pragma Warnings (Off);
--  ??? Why.Sinfo" is directly visible as "Sinfo", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Sinfo"). Maybe we should think of renaming it to
--  "Why.W_Sinfo".
with Why.Sinfo;                          use Why.Sinfo;
pragma Warnings (On);
with Why.Ids;                            use Why.Ids;
with Why.Types;                          use Why.Types;
with Common_Containers;                  use Common_Containers;
with Gnat2Why.Util;                      use Gnat2Why.Util;

package Why.Inter is
   --  This package contains types that are used to represent intermediate
   --  phases of the translation process.

   type Theory_Kind is
     (Standalone_Theory,      --  standalone definition of symbols
      Definition_Theory,      --  definition of symbols
      Axiom_Theory,           --  axioms for previously defined symbols
      VC_Generation_Theory);  --  generation of VCs

   function Compute_Ada_Nodeset (W : Why_Node_Id) return Node_Sets.Set;
   --  For a given Why node, compute the required Ada nodes, from which we can
   --  compute the necessary inclusions on the Why side

   procedure Close_Theory
     (P              : in out Why_Section;
      Kind           : Theory_Kind;
      Defined_Entity : Entity_Id := Empty);
   --  Close the current theory by adding all necessary imports and adding
   --  the theory to the file. If not Empty, Defined_Entity is the entity
   --  defined by the current theory, which is used to complete the graph
   --  of dependencies for this entity. If Do_Closure is True, then these
   --  dependencies are used to get all entities on which this definition
   --  depends. With_Completion is True if the completion theories should be
   --  added too.

   procedure Add_Extra_Dependency
     (Defined_Entity : Entity_Id;
      New_Dependency : Entity_Id);
   --  Add an extra dependency New_Dependency for entity Defined_Entity

   procedure Discard_Theory (P : in out Why_Section);
   --  Remove the current theory from P

   procedure Open_Theory (P       : in out Why_Section;
                          Name    : String;
                          Comment : String;
                          Kind    : EW_Theory_Type := EW_Module)
     with Pre => (P.Cur_Theory = Why_Empty);
   --  Open a new theory in the file.

   procedure Add_Use_For_Entity
     (P               : Why_Section;
      N               : Entity_Id;
      Use_Kind        : EW_Clone_Type := EW_Clone_Default;
      With_Completion : Boolean := True);
   --  For the given entity, add a use clause to the current theory.
   --  With_Completion is True if the completion theories for N should be
   --  added too.

   procedure Add_Effect_Imports (P : Why_Section;
                                 S : Name_Set.Set);

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module);

   procedure Add_With_Clause (P        : Why_Section;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module);

   procedure Add_Effect_Imports (T : W_Theory_Declaration_Id;
                                 S : Name_Set.Set);
   --  Add all import clauses that are necessary for the given set of variables

   function Dispatch_Entity (E : Entity_Id) return Why_Section_Enum;
   --  Given an Ada Entity, return the appropriate Why File to insert the
   --  entity.

   function Dispatch_Entity_Completion (E : Entity_Id) return Why_Section_Enum;
   --  Given an Ada Entity, return the appropriate Why File to insert the
   --  completion theory for the entity.

   function To_Why_Id (E      : Entity_Id;
                       Domain : EW_Domain := EW_Prog;
                       Local  : Boolean := False;
                       Rec    : Entity_Id := Empty;
                       Typ    : W_Type_Id := Why_Empty) return W_Identifier_Id;
   --  The one and only way to transform an Ada Entity to a Why identifier.
   --  However, sometimes the exact way differs between program and logic world
   --  There is also a local and a global name of each identifier. The local
   --  name is to be used when referring to the entity in the Why3 module in
   --  which it is being defined. The global name is to be used everywhere
   --  else.
   --  The Rec entity is used only for record components and specifies the
   --  (sub-)type which contains the component.

   function To_Why_Id (Obj : String; Local : Boolean) return W_Identifier_Id;
   --  This function should only be called for object references for effects

   function To_Why_Type (T : String) return W_Identifier_Id;

   function EW_Bool_Type return W_Type_Id;
   function EW_Int_Type return W_Type_Id;
   function EW_Fixed_Type return W_Type_Id;
   function EW_Real_Type return W_Type_Id;
   function EW_Private_Type return W_Type_Id;
   function EW_Unit_Type return W_Type_Id;
   function EW_Prop_Type return W_Type_Id;
   function Why_Types (E : EW_Basic_Type) return W_Type_Id;

   function EW_Abstract (N : Node_Id) return W_Type_Id;
   --  Convert an Ada type entity into a Why type. This function respects the
   --  gnat2why encoding. For example, for N = Boolean the function returns
   --  EW_Bool_Type, for non-SPARK types and abstract states, EW_Private_Type
   --  is returned. For all the details, see the implementation.

   function EW_Split (N : Node_Id) return W_Type_Id;
   --  This function does the exact same thing as EW_Abstract, but changes the
   --  kind of the node to EW_Split

   function New_Abstract_Base_Type (E : Entity_Id) return W_Type_Id;
   function New_Named_Type (Name : W_Identifier_Id) return W_Type_Id;
   function New_Ref_Type (Ty : W_Type_Id) return W_Type_Id;

   function Type_Of_Node (N : Node_Id) return W_Type_Id;
   --  Given an ada node, try hard to make a type of it. If the node is a type
   --  entity, return the corresponding Why type; if it's an object, return the
   --  Why type of the corresponding Why object.

   function Base_Why_Type (N : Node_Id) return W_Type_Id;
   function Base_Why_Type (W : W_Type_Id) return W_Type_Id;
   --  Return the base type in Why of the given node. This type will be
   --  used for comparisons, conversions etc. Examples are EW_Real_Type
   --  for standard__float, and the Root_Record_Type for record types.

   function Is_Record_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Is_Array_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Is_Private_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Base_Why_Type (Left, Right : W_Type_Id) return W_Type_Id;
   function Base_Why_Type (Left, Right : Node_Id) return W_Type_Id;
   --  Return the most general base type for Left and Right
   --  (e.g. real in Left=int and Right=real).

   function Get_EW_Type (T : W_Type_Id) return EW_Type;
   function Get_EW_Type (T : Node_Id) return EW_Type;
   --  Return the EW_Type of the given entity

   function Up (WT : W_Type_Id) return W_Type_Id;
   --  If WT is the highest base type, return WT; otherwise, return the
   --  smallest base type BT such that WT < BT.

   function Up (From, To : W_Type_Id) return W_Type_Id;
   --  Same as unary Up, except that it stops when To is reached;
   --  i.e. if From = To then To is returned.

   function LCA (Left, Right : W_Type_Id;
                 Force : Boolean := False) return W_Type_Id;
   --  Return the lowest common ancestor in base type hierarchy,
   --  i.e. the smallest base type B such that Left <= B and right <= B.
   --  If Force = True, we also force B to be different from Left or Right,
   --  even in the case Left = Right.

   function Eq_Base_Type (Left, Right : W_Type_Id) return Boolean;
   --  Return True if Left and Right are both W_Type_Id nodes, and Eq
   --  returns True on these seen as W_Type_Id nodes.

   function Eq_Base (Left, Right : W_Type_Id) return Boolean;
   --  Extensional equality (i.e. returns True if Left and Right are of
   --  the same kind, and have the same Ada Node if this kind is EW_Abstract).

   function Eq (Left, Right : Entity_Id) return Boolean;
   --  Return True if Left and Right corresponds to the same Why identifier

private
   Entity_Dependencies : Node_Graphs.Map;
   --  Mapping from an entity to the set of entities on which it depends. This
   --  map is filled by Close_Theory.

   function EW_Bool_Type return W_Type_Id is (Why_Types (EW_Bool));
   function EW_Int_Type return W_Type_Id is (Why_Types (EW_Int));
   function EW_Fixed_Type return W_Type_Id is (Why_Types (EW_Fixed));
   function EW_Private_Type return W_Type_Id is (Why_Types (EW_Private));
   function EW_Prop_Type return W_Type_Id is (Why_Types (EW_Prop));
   function EW_Real_Type return W_Type_Id is (Why_Types (EW_Real));
   function EW_Unit_Type return W_Type_Id is (Why_Types (EW_Unit));

end Why.Inter;
