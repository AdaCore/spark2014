------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W _ T Y P E S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
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

--  This package deals with common types used in flow analysis, in
--  particular Flow_Id and V_Attributes.

with Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Ordered_Sets;
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;              use Ada.Strings.Unbounded;

with Atree;                              use Atree;
with Sinfo;                              use Sinfo;
with Types;                              use Types;

with Gnat2Why.Nodes;                     use Gnat2Why.Nodes;
--  Node_Sets and Node_Hash

with SPARK_Frame_Conditions;             use SPARK_Frame_Conditions;
--  Entity_Name

with Flow_Tree_Utility;                  use Flow_Tree_Utility;

package Flow_Types is

   ----------------------------------------------------------------------
   --  Utility types related to entities and nodes
   ----------------------------------------------------------------------

   package Entity_Lists is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Entity_Id);

   package Ordered_Entity_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Entity_Id,
      "<"          => Lexicographic_Entity_Order,
      "="          => "=");

   package Node_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Node_Or_Entity_Id,
      "="          => "=");

   function To_Ordered_Entity_Set (S : Node_Sets.Set)
                                   return Ordered_Entity_Sets.Set;
   --  Convert a hashed node set into an ordered node set.

   package Unbounded_String_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Unbounded_String);

   ----------------------------------------------------------------------
   --  Flow_Id
   --
   --  Represents an instance of a Node or Entity that is involved
   --  in flow analysis. A reference to just the Entity_Id or Node_Id
   --  is not sufficient, though, in a few cases:
   --    1) Initial and Final values need to be differentiated from
   --       "Normal" use of an entity.
   --    2) Individual record field(s) need to be modelled in addition
   --       to the "entire variable" represented by the Entity_Id.
   --    3) Entities referenced as a result of global-frame-computataion
   --       but are NOT in the AST are represented by a "magic string"
   --       rather than an Entity or Node ID.
   ----------------------------------------------------------------------

   type Param_Mode is (Mode_Invalid,
                       Mode_Proof,
                       Mode_In,
                       Mode_In_Out,
                       Mode_Out);

   subtype In_Global_Modes is Param_Mode
     range Mode_Proof .. Mode_In;

   subtype Initialized_Global_Modes is Param_Mode
     range Mode_Proof .. Mode_In_Out;

   subtype Exported_Global_Modes is Param_Mode
     range Mode_In_Out .. Mode_Out;

   type Edge_Colours is (EC_Default, EC_DDG, EC_TDG);

   type Flow_Id_Kind is (Null_Value,
                         --  No reference or any entity or node

                         Direct_Mapping,
                         --  Direct reference to Entity or Node in the AST

                         Record_Field,
                         --  Reference to list of record field(s) as well
                         --  as whole variable entity in the AST

                         Synthetic_Null_Export,
                         --  The null export (to capture effects, such as
                         --  timing, outside of SPARK)

                         Magic_String
                         --  Entity not in AST, so referred to by a String
                        );

   type Flow_Id_Variant is (
      Normal_Use,
      --  Normal usage of the identifier.

      Initial_Value,
      Final_Value,
      --  For the 'initial and 'final vertices.

      Initial_Grouping,
      Final_Grouping,
      --  For the tree of record components.

      In_View,
      Out_View
      --  For the procedure call parameter vertices.
   );

   subtype Initial_Or_Final_Variant is Flow_Id_Variant
     range Initial_Value .. Final_Value;

   subtype Parameter_Variant is Flow_Id_Variant
     range In_View .. Out_View;

   type Corresponding_Grouping_Map is
     array (Initial_Or_Final_Variant) of Flow_Id_Variant;

   Corresponding_Grouping : constant Corresponding_Grouping_Map :=
     (Initial_Value => Initial_Grouping,
      Final_Value   => Final_Grouping);

   type Flow_Id (Kind : Flow_Id_Kind := Null_Value) is record
      Variant : Flow_Id_Variant;
      case Kind is
         when Direct_Mapping | Record_Field =>
            Node : Node_Or_Entity_Id;

            case Kind is
               when Record_Field =>
                  Component : Entity_Lists.Vector;
               when others =>
                  null;
            end case;

         when Magic_String =>
            Name : Entity_Name;

         when others =>
            null;
      end case;
   end record;

   function "=" (Left, Right : Flow_Id) return Boolean;
   --  Equality for flow id.

   function "<" (Left, Right : Flow_Id) return Boolean;
   --  Ordering for flow id.

   Null_Flow_Id : constant Flow_Id :=
     Flow_Id'(Kind    => Null_Value,
              Variant => Normal_Use);

   Null_Export_Flow_Id : constant Flow_Id :=
     Flow_Id'(Kind    => Synthetic_Null_Export,
              Variant => Normal_Use);

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type;
   --  Hash function for flow id's. The idea is that a direct mapping
   --  to node N will return the same hash as a magic string mapping
   --  to node N.

   function Present (F : Flow_Id) return Boolean
   is (F.Kind /= Null_Value);
   --  Returns true iff F is not null.

   function Synthetic (F : Flow_Id) return Boolean
   is (F.Kind = Synthetic_Null_Export);
   --  Returns true iff F is a synthesised Flow_Id.

   function Direct_Mapping_Id
     (N       : Node_Or_Entity_Id;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id
      with Pre => Present (N);
   --  Create a Flow_Id for the given node or entity.

   function Get_Direct_Mapping_Id
     (F : Flow_Id)
      return Node_Id
      with Pre  => (F.Kind in Direct_Mapping | Record_Field),
           Post => (Present (Get_Direct_Mapping_Id'Result));
   --  Given a direct mapping Flow_Id, return the associated node or
   --  entity. In case of a record field, return the entire variable.

   function Record_Field_Id
     (N       : Node_Id;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id
      with Pre => Present (N) and then Nkind (N) = N_Selected_Component;
   --  Create a Flow_Id for the given record field.

   function Is_Discriminant (F : Flow_Id) return Boolean;
   --  Returns true if the given flow id is a record field
   --  representing a discriminant.

   function Get_Default_Initialization (F : Flow_Id) return Node_Id;
   --  Get the default initialization expression for the given flow id
   --  (this only really works for record fields and direct mappings;
   --  magic strings are assumed to not be default initialized)

   function Is_Default_Initialized (F : Flow_Id) return Boolean;
   --  As above, but can also return true if we can't actually get a node
   --  which is the default-initialized expression.

   function Is_Volatile (F : Flow_Id) return Boolean;
   --  Returns true if the given flow id is volatile in any way.

   function Has_Async_Readers (F : Flow_Id) return Boolean
   with Post => (if Has_Async_Readers'Result then Is_Volatile (F));
   --  Checks if F has async readers.

   function Has_Async_Writers (F : Flow_Id) return Boolean
   with Post => (if Has_Async_Writers'Result then Is_Volatile (F));
   --  Checks if F has async writers.

   function Has_Effective_Reads (F : Flow_Id) return Boolean
   with Post => (if Has_Effective_Reads'Result then Has_Async_Writers (F));
   --  Checks if reads of F are always effective.

   function Has_Effective_Writes (F : Flow_Id) return Boolean
   with Post => (if Has_Effective_Writes'Result then Has_Async_Readers (F));
   --  Checks if writes to F are always effective.

   function Is_Abstract_State (F : Flow_Id) return Boolean;
   --  Checks if F is an abstract state.

   function Magic_String_Id
     (S       : Entity_Name;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id;
   --  Create a Flow_Id for the given magic string.

   function Change_Variant (F       : Flow_Id;
                            Variant : Flow_Id_Variant)
                            return Flow_Id;
   --  Returns a copy of the given flow id, but with a modified
   --  variant.

   function Parent_Record (F : Flow_Id) return Flow_Id
     with Pre  => F.Kind = Record_Field,
          Post => Parent_Record'Result.Kind in Direct_Mapping | Record_Field;
   --  Return the parent record for the given record field.

   function Entire_Variable (F : Flow_Id) return Flow_Id
     with Post => Entire_Variable'Result.Kind /= Record_Field;
   --  Returns the entire variable represented by F.

   procedure Sprint_Flow_Id (F : Flow_Id);
   --  Debug procedure to print the given flow id, similar to
   --  Sprint_Node.

   procedure Print_Flow_Id (F : Flow_Id);
   --  Debug procedure to print the flow id with more information
   --  (such as kind and variant) attached.

   function Flow_Id_To_String (F : Flow_Id) return String
     with Pre => Is_Easily_Printable (F);
   --  Convert a flow id to a human readable string. This is used for
   --  emitting error messages.

   function Is_Easily_Printable (F : Flow_Id) return Boolean;
   --  Check if F can be printed without resorting to Sprint.

   ----------------------------------------------------------------------
   --  Types based on Flow_Id
   ----------------------------------------------------------------------

   package Flow_Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Ordered_Flow_Id_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Flow_Id,
      "<"          => "<",
      "="          => "=");

   function To_Ordered_Flow_Id_Set (S : Flow_Id_Sets.Set)
                                    return Ordered_Flow_Id_Sets.Set;
   --  Convert a hashed flow id set into an ordered node set.

   function To_Entire_Variables (S : Flow_Id_Sets.Set)
                                 return Flow_Id_Sets.Set
     with Post => (for all X of To_Entire_Variables'Result =>
                     X.Kind /= Record_Field);
   --  Convert a set containing flattened records into a set
   --  containing only entire variables.

   function To_Name_Set (S : Flow_Id_Sets.Set) return Name_Set.Set;
   --  Convert a flow id set to a name set. Any record fields are
   --  changed into entire variables.

   function To_Node_Set (S : Flow_Id_Sets.Set) return Node_Sets.Set
     with Pre => (for all F of S => F.Kind = Direct_Mapping);
   --  Convert a simple flow_id set to a node set.

   function To_Flow_Id_Set (S : Node_Sets.Set) return Flow_Id_Sets.Set
     with Post => (for all F of To_Flow_Id_Set'Result =>
                     F.Kind = Direct_Mapping);
   --  Convert a node set to a flow_id set.

   ----------------------------------------------------------------------
   --  V_Attributes
   ----------------------------------------------------------------------

   --  If you change this type, please also update Print_Graph_Vertex in
   --  Flow.

   type Pretty_Print_Kind_T is (Pretty_Print_Null,
                                Pretty_Print_Initializes_Aspect);

   type Execution_Kind_T is (Normal_Execution,
                             Abnormal_Termination,
                             Infinite_Loop);
   --  Please be *exceptionally* alert when adding elements to this type,
   --  as many checks simlpy check for one of the options (and do not
   --  explicitly make sure all cases are considered).

   type V_Attributes is record
      Is_Null_Node        : Boolean;
      --  Set for auxiliary nodes which can be removed, such as early
      --  returns or null statements.

      Is_Program_Node     : Boolean;
      --  Set for all vertices which both
      --     - trace directly to an element in the AST,
      --     - they are constructs which could be ineffective
      --
      --  Setting this attribute enables the following analyses which
      --  would not normally be performed:
      --     * ineffective_statements
      --
      --  It should be noted that most vertices we construct will have
      --  this set to true.

      Is_Precondition     : Boolean;
      --  True if this vertex represents the precondition.

      Is_Default_Init     : Boolean;
      --  True if this vertex represents a default initialization.

      Is_Loop_Entry       : Boolean;
      --  True if this vertex represents a loop entry assignment. For
      --  each variable where we use 'Loop_Entry we have one of these
      --  at the top of the actual loop.

      Is_Initialized      : Boolean;
      --  True if an initial value is either imported (in or in out)
      --  or otherwise initialized.

      Is_Function_Return  : Boolean;
      --  True if this vertex models the returned value of a function.

      Is_Global           : Boolean;
      --  True if the imported or exported variable is a global.

      Is_Loop_Parameter   : Boolean;
      --  True for loop parameters so they can be ignored in
      --  ineffective-import analysis.

      Is_Import           : Boolean;
      --  True if the given initial value is a parameter or global of
      --  the analysed subprogram.

      Is_Export           : Boolean;
      --  True if the given final-use variable is actually relevant to
      --  a subprogram's exports (out parameter or global out).

      Mode                : Param_Mode;
      --  Set for initial and final use vertices which are parameters
      --  or globals.

      Is_Package_State    : Boolean;
      --  True if the given variable is part of a package' state.

      Is_Constant         : Boolean;
      --  True if this value may not be updated.

      Is_Callsite         : Boolean;
      --  True if the vertex represents a subprogram call.

      Is_Parameter        : Boolean;
      --  True if this vertex models an argument to a procedure call.

      Is_Discriminants_Only_Parameter : Boolean;
      --  If true this only captures the discriminants.

      Is_Global_Parameter : Boolean;
      --  True if this vertex models a global for a procedure or
      --  function call.

      Execution           : Execution_Kind_T;
      --  Determines how we should treat edges from this vertex. Most nodes
      --  will have Normal_Execution set here.

      Perform_IPFA        : Boolean;
      --  True if the dependencies for this callsite should be filled
      --  in using interprocedural flow analysis.

      Call_Vertex         : Flow_Id;
      --  Used to identify which vertex a parameter vertex belongs to.

      Parameter_Actual    : Flow_Id;
      Parameter_Formal    : Flow_Id;
      --  For nodes where Is_Parameter is true, this keeps track of which
      --  parameter this is. This is also quite useful for pretty-printing.
      --  For nodes with Is_Global_Parameter only Parameter_Formal is set.

      Default_Init_Var    : Flow_Id;
      Default_Init_Val    : Node_Id;
      --  For default initializations (Is_Default_init) this pair
      --  records which variable has a default value (Var) and what it
      --  is (Val).

      Variables_Defined   : Flow_Id_Sets.Set;
      Variables_Used      : Flow_Id_Sets.Set;
      --  For producing the DDG.

      Variables_Explicitly_Used : Flow_Id_Sets.Set;
      --  Similar to Variables_Used, but does not include the implicit
      --  self-dependency for partial record and array updates.

      Volatiles_Read      : Flow_Id_Sets.Set;
      Volatiles_Written   : Flow_Id_Sets.Set;
      --  Again, for producing the DDG. These are implied updates due
      --  to reads of volatiles where reads are effective.

      Loops               : Node_Sets.Set;
      --  Which loops are we a member of (identified by loop
      --  name/label). For loop stability analysis.

      Error_Location      : Node_Or_Entity_Id;
      --  If we have an error involving this vertex, raise it here.

      Aux_Node            : Node_Or_Entity_Id;
      --  The meaning of this depends on the kind of vertex these
      --  attributes are attached to.
      --
      --     * E_Return_Statement: for the implicit extended return
      --       returns this keeps track of the actual variable we return.

      Pretty_Print_Kind   : Pretty_Print_Kind_T;
      --  Some extra information which we use when deciding how to pretty
      --  print the vertex in --flow-debug mode.
   end record;
   pragma Pack (V_Attributes);

   Null_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node                    => False,
                   Is_Program_Node                 => False,
                   Is_Precondition                 => False,
                   Is_Default_Init                 => False,
                   Is_Loop_Entry                   => False,
                   Is_Initialized                  => False,
                   Is_Function_Return              => False,
                   Is_Global                       => False,
                   Is_Loop_Parameter               => False,
                   Is_Import                       => False,
                   Is_Export                       => False,
                   Mode                            => Mode_Invalid,
                   Is_Package_State                => False,
                   Is_Constant                     => False,
                   Is_Callsite                     => False,
                   Is_Parameter                    => False,
                   Is_Discriminants_Only_Parameter => False,
                   Is_Global_Parameter             => False,
                   Execution                       => Normal_Execution,
                   Perform_IPFA                    => False,
                   Call_Vertex                     => Null_Flow_Id,
                   Parameter_Actual                => Null_Flow_Id,
                   Parameter_Formal                => Null_Flow_Id,
                   Default_Init_Var                => Null_Flow_Id,
                   Default_Init_Val                => Empty,
                   Variables_Defined               => Flow_Id_Sets.Empty_Set,
                   Variables_Used                  => Flow_Id_Sets.Empty_Set,
                   Variables_Explicitly_Used       => Flow_Id_Sets.Empty_Set,
                   Volatiles_Read                  => Flow_Id_Sets.Empty_Set,
                   Volatiles_Written               => Flow_Id_Sets.Empty_Set,
                   Loops                           => Node_Sets.Empty_Set,
                   Error_Location                  => Empty,
                   Aux_Node                        => Empty,
                   Pretty_Print_Kind               => Pretty_Print_Null);

   Null_Node_Attributes : constant V_Attributes :=
     Null_Attributes'Update (Is_Null_Node    => True,
                             Is_Program_Node => True);

end Flow_Types;
