------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Common_Containers;    use Common_Containers;
with GNATCOLL.Symbols;     use GNATCOLL.Symbols;
with Gnat2Why.Util;        use Gnat2Why.Util;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Why.Ids;              use Why.Ids;
with Why.Types;            use Why.Types;

pragma Warnings (Off);
--  ??? Why.Sinfo" is directly visible as "Sinfo", as it has "Why" as a
--  common ancestor with the current package. So it hides compilation unit
--  with the same name ("Sinfo"). Maybe we should think of renaming it to
--  "Why.W_Sinfo".
with Why.Sinfo;         use Why.Sinfo;
pragma Warnings (On);

package Why.Inter is
   --  This package contains types that are used to represent intermediate
   --  phases of the translation process.

   type Theory_Kind is
     (Standalone_Theory,      --  standalone definition of symbols
      Definition_Theory,      --  definition of symbols
      Axiom_Theory,           --  axioms for previously defined symbols
      VC_Generation_Theory);  --  generation of VCs

   function Compute_Module_Set (W : Why_Node_Id) return Why_Node_Sets.Set;
   --  For a given Why node, compute the required modules, to be included to
   --  make this Why node a valid node.

   function Compute_Ada_Node_Set (W : Why_Node_Id) return Node_Sets.Set
   with Post => (for all N of Compute_Ada_Node_Set'Result => Present (N));

   procedure Close_Theory
     (Th             : in out Theory_UC;
      Kind           : Theory_Kind;
      Defined_Entity : Entity_Id := Empty)
   with Post => Th.Finished = True;
   --  Close the current theory by adding all necessary imports and adding
   --  the theory to the file. If not Empty, Defined_Entity is the entity
   --  defined by the current theory, which is used to complete the graph
   --  of dependencies for this entity.

   function Open_Theory
     (P       : W_Section_Id;
      Module  : W_Module_Id;
      Comment : String)
     return Theory_UC
     with Post => Open_Theory'Result.Finished = False;
   --  Open a new theory in the file

   function Find_Decl (S : Symbol) return W_Theory_Declaration_Id;
   --  Return the Theory Declaration that defines the theory with the name S

   procedure Add_Use_For_Entity
     (Th              : Theory_UC;
      E               : Entity_Id;
      Use_Kind        : EW_Clone_Type := EW_Clone_Default;
      With_Completion : Boolean := True);
   --  For the given entity, add a use clause to the current theory.
   --  With_Completion is True if the completion theories for E should be
   --  added too.

   procedure Add_With_Clause
     (T        : Theory_UC;
      Module   : W_Module_Id;
      Use_Kind : EW_Clone_Type);
   --  Add use clause for Module to the list of declarations from T.
   --  @param T the theory where the use clause will be emitted
   --  @param Module module that we want to use
   --  @param Use_Kind kind of Why3 use clause. It will be overrdidden to
   --     Import for Int_Module and RealInfix modules to allow infix notations.

   function Goto_Exception_Name (E : Entity_Id) return W_Name_Id
   with Pre => Ekind (E) = E_Label;

   function Loop_Exception_Name
     (E     : Entity_Id;
      Local : Boolean := False)
      return W_Name_Id
   with Pre => Ekind (E) = E_Loop;
   --  Transform a loop entity into a name for a Why exception

   --  A given subprogram declaration in SPARK may be translated into multiple
   --  variants in Why3, with different contracts. This type defines the
   --  variants that may be used. For each applicable variant, a namespace is
   --  defined in the module for the function, with the specialized definitions
   --  inside the namespace. This allows using the same name for the different
   --  variants.
   type Selection_Kind is
     (Standard,   --  Standard variant of the program function (defined outside
                  --  any namespace, directly in the module for the program
                  --  function).

      Dispatch,   --  Variant of the program function used when the call is
                  --  dispatching. It has the appropriate contract.

      No_Return,  --  Variant of the program function used when calling
                  --  an error-signaling procedure outside another
                  --  error-signaling procedure. It has a precondition of
                  --  False. This ensures that a check is issued for each
                  --  such call, to detect when they are reachable.

      Refine);    --  Variant of the program function used when the call
                  --  has visibility over the refined postcondition of the
                  --  subprogram. It has the appropriate refined contract.

   function To_Why_Id
     (E            : Entity_Id;
      Domain       : EW_Domain := EW_Prog;
      Local        : Boolean := False;
      Selector     : Selection_Kind := Standard;
      No_Comp      : Boolean := False;
      Rec          : Entity_Id := Empty;
      Typ          : W_Type_Id := Why_Empty;
      Relaxed_Init : Boolean := False) return W_Identifier_Id
   with Pre => Ekind (E) in Subprogram_Kind
                          | Entry_Kind
                          | Named_Kind
                          | Type_Kind
                          | Object_Kind;
   --  The one and only way to transform an Ada Entity to a Why identifier.
   --  However, sometimes the exact way differs between program and logic
   --  worlds. There is also a local and a global name of each identifier. The
   --  local name is to be used when referring to the entity in the Why3 module
   --  in which it is being defined. The global name is to be used everywhere
   --  else.
   --  There may be several ways to refer to an Ada Name, especially for
   --  subprograms. A call may use the refined contracts, or the dispatching
   --  contracts.
   --  @param E Entity to be translated
   --  @param Domain Domain of the id
   --  @param Local Wether we want the local or the global name
   --  @param Selector Selects the proper version of a subprogram
   --  @param No_Comp Translates record fields and discriminants as normal
   --         names.
   --  @param Rec Record entity that is used only for record components and
   --         specifies the (sub-)type which contains the component.
   --  @param Typ Expected type of the id.
   --  @param Relaxed_Init True if the identifier should be located in the
   --         module for the init wrapper type.
   --  @result The Why identifier to be used for E.

   function To_Why_Id
     (Obj   : Entity_Name;
      Local : Boolean)
      return W_Identifier_Id;
   --  This function should only be called for object references for effects

   function To_Why_Type
     (E            : Entity_Id;
      Local        : Boolean := False;
      Relaxed_Init : Boolean := False) return W_Name_Id
   with Pre => Is_Type (E);

   function EW_Abstract
     (N : Node_Id; Relaxed_Init : Boolean := False) return W_Type_Id
   with Pre => Is_Type (N);
   --  Convert an Ada type entity into a Why type. This function respects the
   --  gnat2why encoding. For example, for N = Boolean the function returns
   --  EW_Bool_Type. For all the details, see the implementation.

   function EW_Fixed_Type (E : Entity_Id) return W_Type_Id with
     Pre => Has_Fixed_Point_Type (E);
   --  Return Why type for fixed point types with the same small as E. These
   --  types are always renamings of Main.__fixed, but they have an Ada node
   --  which may be used to retrieve the appropriate conversion functions.

   function EW_Split
     (N : Node_Id; Relaxed_Init : Boolean := False) return W_Type_Id
   with Pre => Is_Type (N);
   --  This function does the exact same thing as EW_Abstract, but changes the
   --  kind of the node to EW_Split.

   function New_Abstract_Base_Type (E : Entity_Id) return W_Type_Id;
   function New_Named_Type (S : String) return W_Type_Id;
   function New_Named_Type
     (Name : W_Name_Id; Relaxed_Init : Boolean := False) return W_Type_Id;
   function New_Ref_Type (Ty : W_Type_Id) return W_Type_Id;

   function Type_Of_Node (N : Node_Id) return W_Type_Id;
   --  Given an Ada node, try hard to make a type of it. If the node is a type
   --  entity, return the corresponding Why type; if it's an object, return the
   --  Why type of the corresponding Why object.

   function Base_Why_Type (N : Node_Id) return W_Type_Id;
   function Base_Why_Type (W : W_Type_Id) return W_Type_Id;
   --  Return the base type in Why of the given node. This type will be
   --  used for comparisons, conversions etc. Examples are EW_Real_Type
   --  for standard__float, and the Root_Retysp for record types.

   function Base_Why_Type_No_Bool (N : Node_Id) return W_Type_Id;
   --  @param N an Ada Node
   --  @return EW_Int_Type if the Base_Why_Type of N is EW_Bool_Type, otherwise
   --    return the Base_Why_Type

   function Base_Why_Type_No_Bool (Typ : W_Type_Id) return W_Type_Id;

   function Base_Why_Type_No_Bool (Expr : W_Expr_Id) return W_Type_Id;

   function Is_Pointer_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Is_Subp_Pointer_Conversion
     (Left, Right : W_Type_Id) return Boolean;

   function Is_Record_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Is_Array_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Is_Private_Conversion (Left, Right : W_Type_Id) return Boolean;

   function Base_Why_Type (Left, Right : W_Type_Id) return W_Type_Id;
   function Base_Why_Type (Left, Right : Node_Id) return W_Type_Id;
   --  Return the most general base type for Left and Right
   --  (e.g. real in Left=int and Right=real).

   function Get_EW_Type (T : Node_Id) return EW_Type;
   --  Return the EW_Type of the given entity

   function Get_EW_Term_Type (N : Node_Id) return W_Type_Id;
   --  If the node is of some scalar type, return the corresponding Why
   --  representation type. Otherwise return the empty node.

   function Eq_In_Why (Left, Right : W_Type_Id) return Boolean;
   --  @param Left Type Id to be compared with
   --  @param Right
   --  @return Returns True if the type output in Why is the same

   function Eq_Base (Left, Right : W_Type_Id) return Boolean;
   --  @param Left Type Id to be compared with
   --  @param Right
   --  @return Returns True if the type Ids have the same structure.

   procedure Record_Extra_Dependency
     (Defining_Module : W_Module_Id;
      Axiom_Module    : W_Module_Id);
   --  Record an extra dependency between Defining_Module and Axiom_Module so
   --  the second is withed along with the first in VC modules.

   procedure Register_Dependency_For_Soundness (M : W_Module_Id;
                                                E : Entity_Id);
   --  Register that M is an axiom module for E. This is used for cycle
   --  detection.

   procedure Check_Safe_Guard_Cycles;
   --  This should be called when all modules have been generated. This
   --  subprogram considers cycles in the graph whose nodes are subprogram
   --  entities, and there is a directed edge between two entities if one
   --  includes the post axiom of the other. Generate a warning for cycles in
   --  this graph.
   --  These cycles correspond to post axioms of entities used to prove
   --  properties of the entity itself, possibly via the proof of other
   --  entities.

private
   Module_Dependencies : Why_Node_Graphs.Map;
   --  Mapping from an module to the set of modules on which it depends. This
   --  map is filled by Close_Theory.

end Why.Inter;
