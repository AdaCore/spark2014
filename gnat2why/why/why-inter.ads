------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Ada.Containers.Hashed_Maps;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Strings.Unbounded;              use Ada.Strings.Unbounded;
with Ada.Strings.Unbounded.Hash;

with SPARK_Frame_Conditions;             use SPARK_Frame_Conditions;

with Atree;                              use Atree;
with Sinfo;                              use Sinfo;
with Types;                              use Types;
pragma Warnings (Off);
--  ??? Why.Sinfo" is directly visible as "Sinfo", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Sinfo"). Maybe we should think of renaming it to
--  "Why.W_Sinfo".
with Why.Sinfo;                          use Why.Sinfo;
pragma Warnings (On);
with Why.Ids;                            use Why.Ids;
with Why.Atree.Builders;                 use Why.Atree.Builders;
with Why.Types;                          use Why.Types;

with Gnat2Why.Nodes;                     use Gnat2Why.Nodes;

package Why.Inter is
   --  This package contains types that are used to represent intermediate
   --  phases of the translation process.

   --  Kinds of Why files ordered by possible inclusion. A file of greater kind
   --  can include files of the same or lower kind.
   type Why_File_Enum is
     (WF_Pure,
      WF_Variables,
      WF_Context,
      WF_Main);

   type Why_File is tagged
      record
         File        : W_File_Id;
         Kind        : Why_File_Enum;
         Cur_Theory  : W_Theory_Declaration_Id;
      end record;
   --  Making this type tagged is a way to force by-reference passing of
   --  objects of this type. This is needed because we have aliasing between
   --  parameters of many functions and the global variable Why_Files below.

   function Make_Empty_Why_File
     (Kind : Why_File_Enum) return Why_File
   with Post => (Make_Empty_Why_File'Result.Cur_Theory = Why_Empty);
   --  Return an empty Why_File with the given name and kind

   procedure Close_Theory
     (P               : in out Why_File;
      Filter_Entity   : Entity_Id;
      Defined_Entity  : Entity_Id := Empty;
      Do_Closure      : Boolean := False;
      No_Import       : Boolean := False;
      With_Completion : Boolean := True);
   --  Close the current theory by adding all necessary imports and adding
   --  the theory to the file. If not Empty, Defined_Entity is the entity
   --  defined by the current theory, which is used to complete the graph
   --  of dependencies for this entity. If Do_Closure is True, then these
   --  dependencies are used to get all entities on which this definition
   --  depends. With_Completion is True if the completion theories should be
   --  added too.

   procedure Discard_Theory (P : in out Why_File);
   --  Remove the current theory from P

   procedure Open_Theory (P       : in out Why_File;
                          Name    : String;
                          Comment : String;
                          Kind    : EW_Theory_Type := EW_Module)
     with Pre => (P.Cur_Theory = Why_Empty);
   --  Open a new theory in the file.

   procedure Add_With_Clause (P        : Why_File;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module);

   procedure Add_Use_For_Entity
     (P               : Why_File;
      N               : Entity_Id;
      Use_Kind        : EW_Clone_Type := EW_Clone_Default;
      With_Completion : Boolean := True);
   --  For the given entity, add a use clause to the current theory. If
   --  Use_Kind is set to EW_Clone_Default, the actual use kind for that
   --  entity is computed from the entity itself. If another value is given for
   --  Use_Kind, that value is used. With_Completion is True if the completion
   --  theories for N should be added too.

   procedure Add_Effect_Imports (P : Why_File;
                                 S : Name_Set.Set);

   Why_Files : array (Why_File_Enum) of Why_File;
   Why_File_Name : String_Access;

   Why_File_Suffix : constant String := ".mlw";

   -----------------
   -- Completions --
   -----------------

   --  Some entities are defined in more than one module. There might be one or
   --  two additional modules, one in the contextual file for the spec, and
   --  one in the contextual file for the body. For each additional module,
   --  Add_Completion is called to record that completion. Later, when a
   --  dependence on this entity is noted, Get_Completions is called to
   --  retrieve the names of the additional modules to include.

   --  This mechanism is also used to trace the dependence between an instance
   --  of a generic package with a Why axiomatization and the expression
   --  functions coming from its actuals.

   subtype Why_Context_File_Enum is Why_File_Enum range
     WF_Pure .. WF_Context;

   type Why_File_Completion_Item is record
      Name : Unbounded_String;
      Kind : Why_Context_File_Enum;
   end record;

   type Why_Completions is array (Positive range <>) of
     Why_File_Completion_Item;
   --  Return type of Get_Completions, to get all completions of a theory

   procedure Add_Completion
     (Name            : String;
      Completion_Name : String;
      Kind            : Why_Context_File_Enum);
   --  Add the completion Completion_Name to theory Name

   function Get_Completions
     (Name       : String;
      Up_To_Kind : Why_File_Enum) return Why_Completions;
   --  Return the completions for the theory called Name, in a file of kind
   --  Why_File_Enum, so only completions of kinds less than Why_File_Enum are
   --  taken into account, to avoid circularities in Why file dependences.

   Standard_Why_Package_Name : constant String := "_standard";

   procedure Init_Why_Files (Unit : Node_Id);
   procedure Init_Why_Files (Prefix : String);
   --  Call this procedure to initialize the predefined Why_Files
   --  The "String" variant uses the same prefix for all files. The other one
   --  uses the spec or body prefix as appropriate.

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module);

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module);
   --  Add a package name to the context of a Why package.

   function File_Base_Name_Of_Entity (E : Entity_Id) return String;
   --  return the base name of the unit in which the entity is
   --  defined

   function Name_Of_Node (N : Node_Id) return String;
   --  Return the uncapitalized name which needs to be used to include the
   --  Why entity for that node (after capitalization).

   procedure Add_Effect_Imports (T : W_Theory_Declaration_Id;
                                 S : Name_Set.Set);
   --  Add all import clauses that are necessary for the given set of variables

   function Dispatch_Entity (E : Entity_Id) return Why_File_Enum;
   --  Given an Ada Entity, return the appropriate Why File to insert the
   --  entity.

   function Dispatch_Entity_Completion (E : Entity_Id) return Why_File_Enum;
   --  Given an Ada Entity, return the appropriate Why File to insert the
   --  completion theory for the entity.

   function To_Why_Id (E      : Entity_Id;
                       Domain : EW_Domain := EW_Prog;
                       Local  : Boolean := False;
                       Rec    : Entity_Id := Empty) return W_Identifier_Id;
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

   EW_Bool_Type : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Bool);
   EW_Int_Type  : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Int);
   EW_Real_Type : constant W_Base_Type_Id :=
                    New_Base_Type (Base_Type => EW_Real);
   EW_Private_Type : constant W_Base_Type_Id :=
                       New_Base_Type (Base_Type => EW_Private);

   type Why_Scalar_Or_Array_Type_Array is
     array (EW_Scalar_Or_Array_Or_Private) of W_Base_Type_Id;

   Why_Types : constant Why_Scalar_Or_Array_Type_Array :=
                 (EW_Bool    => EW_Bool_Type,
                  EW_Int     => EW_Int_Type,
                  EW_Real    => EW_Real_Type,
                  EW_Private => EW_Private_Type);

   function EW_Abstract (N : Node_Id) return W_Base_Type_Id;

   function Base_Why_Type (N : Node_Id) return W_Base_Type_Id;
   function Base_Why_Type (W : W_Base_Type_Id) return W_Base_Type_Id;
   --  Return the base type in Why of the given node. This type will be
   --  used for comparisons, conversions etc. Examples are EW_Real_Type
   --  for standard__float, and the Root_Record_Type for record types.

   function Is_Record_Conversion (Left, Right : W_Base_Type_Id) return Boolean;

   function Is_Array_Conversion (Left, Right : W_Base_Type_Id) return Boolean;

   function Base_Why_Type (Left, Right : W_Base_Type_Id) return W_Base_Type_Id;
   function Base_Why_Type (Left, Right : Node_Id) return W_Base_Type_Id;
   --  Return the most general base type for Left and Right
   --  (e.g. real in Left=int and Right=real).

   function Get_EW_Type (T : W_Primitive_Type_Id) return EW_Type;
   function Get_EW_Type (T : Node_Id) return EW_Type;
   --  Return the EW_Type of the given entity

   function Up (WT : W_Base_Type_Id) return W_Base_Type_Id;
   --  If WT is the highest base type, return WT; otherwise, return the
   --  smallest base type BT such that WT < BT.

   function Up (From, To : W_Base_Type_Id) return W_Base_Type_Id;
   --  Same as unary Up, except that it stops when To is reached;
   --  i.e. if From = To then To is returned.

   function  LCA (Left, Right : W_Base_Type_Id;
                  Force : Boolean := False) return W_Base_Type_Id;
   --  Return the lowest common ancestor in base type hierarchy,
   --  i.e. the smallest base type B such that Left <= B and right <= B.
   --  If Force = True, we also force B to be different from Left or Right,
   --  even in the case Left = Right.

   function Full_Name (N : Entity_Id) return String
      with Pre => (Nkind (N) in N_Entity);
   --  Given an N_Entity, return its Full Name, as used in Why.

   function Full_Name_Is_Not_Unique_Name (N : Entity_Id) return Boolean;
   --  The full name of an entity is based on its unique name in nearly all
   --  cases, so that this name can be used e.g. to retrieve completion
   --  theories. In a few cases which require special handling
   --  (currently Standard_Boolean and Universal_Fixed), the full name is hard
   --  coded for Why, so should not be used as a representative of the entity.

   function Eq_Base_Type (Left, Right : W_Primitive_Type_Id) return Boolean;
   --  Return True if Left and Right are both W_Base_Type_Id nodes, and Eq
   --  returns True on these seen as W_Base_Type_Id nodes.

   function Eq (Left, Right : W_Base_Type_Id) return Boolean;
   --  Extensional equality (i.e. returns True if Left and Right are of
   --  the same kind, and have the same Ada Node if this kind is EW_Abstract).

   function Eq (Left, Right : Entity_Id) return Boolean;
   --  Return True if Left and Right corresponds to the same Why identifier

private
   package Why_File_Completion_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type    => Why_File_Completion_Item,
      "="             => "=");

   package Why_File_Completions is new Ada.Containers.Hashed_Maps
     (Key_Type        => Unbounded_String,
      Element_Type    => Why_File_Completion_Lists.List,
      Hash            => Ada.Strings.Unbounded.Hash,
      Equivalent_Keys => "=",
      "="             => Why_File_Completion_Lists."=");
   --  Data type storing chained completions of theories

   Why_File_Completion : Why_File_Completions.Map;
   --  Global variable storing completions of theories

   Entity_Dependencies : Node_Graphs.Map;
   --  Mapping from an entity to the set of entities on which it depends. This
   --  map is filled by Close_Theory.

end Why.Inter;
