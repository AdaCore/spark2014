------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           F L O W _ T Y P E S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2021, Altran UK Limited                --
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

--  This package deals with common types used in flow analysis, in particular
--  Flow_Id and V_Attributes.

with Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Ordered_Sets;
with Atree;                       use Atree;
with Common_Containers;           use Common_Containers;
with Einfo;                       use Einfo;
with Graphs;
with Sinfo;                       use Sinfo;
with SPARK_Util;                  use SPARK_Util;
with Types;                       use Types;

package Flow_Types is

   type Analyzed_Subject_Kind is (Kind_Subprogram,
                                  Kind_Task,
                                  Kind_Package);
   --  The different kinds of things we will analyze

   ----------------------------------------------------------------------
   --  Flow_Id
   --
   --  Represents an instance of a Node or Entity that is involved in flow
   --  analysis. A reference to just the Entity_Id or Node_Id is not
   --  sufficient, though, in a few cases:
   --    1) Initial and Final values need to be differentiated from "Normal"
   --       use of an entity.
   --    2) Individual record field(s) need to be modelled in addition to the
   --       "entire variable" represented by the Entity_Id.
   --    3) Entities referenced as a result of global-frame-computataion but
   --       are NOT in the AST are represented by a "magic string" rather than
   --       an Entity or Node ID.
   ----------------------------------------------------------------------

   type Param_Mode is (Mode_Invalid,
                       Mode_Proof,
                       Mode_In,
                       Mode_In_Out,
                       Mode_Out);
   pragma Ordered (Param_Mode);

   subtype In_Global_Modes is Param_Mode
     range Mode_Proof .. Mode_In;

   subtype Initialized_Global_Modes is Param_Mode
     range Mode_Proof .. Mode_In_Out;

   subtype Exported_Global_Modes is Param_Mode
     range Mode_In_Out .. Mode_Out;

   type Edge_Colours is (EC_Default,
                         --  Control-flow dependencies

                         EC_Barrier,
                         --  For the `wait' edges for barriers. They introduce
                         --  control dependence, but are otherwise not
                         --  traversible.

                         EC_Abend,
                         --  For abnormal termination we need to add an edge,
                         --  but it should not be traversed for the purpose of
                         --  producing the DDG.

                         EC_Inf,
                         --  For infinite loops we do add an edge, but we do
                         --  not want to traverse it for the purpose of finding
                         --  dead code.

                         EC_DDG,
                         --  Data dependencies

                         EC_TDG
                         --  Transitive call dependencies
                        );
   --  ??? by convention type name are in singular (e.g. Kind not Kinds)

   type Flow_Id_Kind is (Null_Value,
                         --  No reference or any entity or node

                         Direct_Mapping,
                         --  Direct reference to Entity or Node in the AST

                         Record_Field,
                         --  Reference to list of record field(s) as well as
                         --  whole variable entity in the AST.

                         Synthetic_Null_Export,
                         --  The null export (to capture effects, such as
                         --  timing, outside of SPARK).

                         Magic_String
                         --  Entity not in AST, so referred to by a String
                        );

   type Flow_Id_Variant is (
      Normal_Use,
      --  Normal usage of the identifier

      Initial_Value,
      Final_Value,
      --  For the 'initial and 'final vertices

      Initial_Grouping,
      Final_Grouping,
      --  For the tree of record components

      In_View,
      Out_View
      --  For the procedure call parameter vertices
   );
   pragma Ordered (Flow_Id_Variant);

   type Variable_Facet_T is (Normal_Part,
                             Private_Part,    --  for private types
                             Extension_Part,  --  for tagged types
                             The_Tag,         --  for tagged types
                             The_Bounds       --  for unconstrained arrays
                             );
   --  Not all things can be represented by just X. For example a discriminated
   --  private type might need X'Private_Part and X.D. Most Flow_Id objects
   --  will describe the Normal_Part.
   --
   --  Flo's note on naming: I did want to use the name "aspect", but this is
   --  perhaps asking for confusion; hence I went for "facet".

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
      --  In theory this doesn't have to be part of a Null_Value id, but there
      --  are many checks for Foo.Variant throughout flow analysis and it will
      --  be quite tedious to prefix each of them with Present (Foo).

      case Kind is
         when Direct_Mapping | Record_Field =>
            Node  : Node_Or_Entity_Id;
            Facet : Variable_Facet_T; --  only used for records and types

            case Kind is
               when Record_Field =>
                  Component : Entity_Vectors.Vector;
               when others =>
                  null;
            end case;

         when Magic_String =>
            Name : Entity_Name;

         when others =>
            null;
      end case;
   end record;

   ----------------
   -- Flow_Scope --
   ----------------

   --  The scopes we care about in flow analysis are restricted to packages,
   --  protected objects and task objects.
   --
   --  Variables or subprograms can be declared or defined in:
   --    * package's visible part
   --    * package's private part
   --    * package's body
   --    * protected object's visible
   --    * protected object's private part
   --    * protected object's body
   --    * task object's visible
   --    * task object's body
   --
   --  Therefore flow scope is an entity + visible|private|body

   type Any_Declarative_Part is
     (Null_Part, Visible_Part, Private_Part, Body_Part);
   pragma Ordered (Any_Declarative_Part);

   subtype Declarative_Part is Any_Declarative_Part range
     Visible_Part .. Body_Part;

   subtype Scope_Id is Entity_Id
   with Dynamic_Predicate =>
     (if Present (Scope_Id)
      then Ekind (Scope_Id) in E_Function
                             | E_Procedure
                             | E_Package
                             | E_Protected_Type
                             | E_Task_Type
                             | Entry_Kind
                             | Generic_Unit_Kind);
   --  Type that defines a subset of legal entities for the use in Flow_Scope

   type Flow_Scope is record
      Ent  : Scope_Id;
      Part : Any_Declarative_Part;
   end record
   with Dynamic_Predicate => (Flow_Scope.Ent = Empty) =
                             (Flow_Scope.Part = Null_Part);
   --  Note: conceptually this is a discrimated record type, but discriminating
   --  on Scope_Id (which is an Entity_Id with a predicate) is troublesome.

   Null_Flow_Scope : constant Flow_Scope := (Empty, Null_Part);

   subtype Global_Set is Node_Sets.Set
   with Dynamic_Predicate =>
          (for all E of Global_Set => Is_Global_Entity (E));

   type Global_Nodes is record
      Proof_Ins : Global_Set;
      Inputs    : Global_Set;
      Outputs   : Global_Set;
   end record
   with Dynamic_Predicate =>
          (for all G of Global_Nodes.Proof_Ins =>
              not Global_Nodes.Inputs.Contains (G) and then
              not Global_Nodes.Outputs.Contains (G));
   --  ??? should it be an array then we could remove some repeated code

   type Global_Names is record
      Proof_Ins : Name_Sets.Set;          --  Flow/User
      Inputs    : Name_Sets.Set;          --  Flow/Frontend/User
      Outputs   : Name_Sets.Set;          --  Flow/Frontend/User
   end record
   with Dynamic_Predicate =>
          (for all G of Global_Names.Proof_Ins =>
              not Global_Names.Inputs.Contains (G) and then
                 not Global_Names.Outputs.Contains (G));

   type Type_Aspect is (No_Aspect, DIC);

   function "=" (Left, Right : Flow_Id) return Boolean;
   --  Equality for Flow_Id

   function "<" (Left, Right : Flow_Id) return Boolean;
   --  Ordering for Flow_Id

   Null_Flow_Id : constant Flow_Id :=
     Flow_Id'(Kind    => Null_Value,
              Variant => Normal_Use);

   Null_Export_Flow_Id : constant Flow_Id :=
     Flow_Id'(Kind    => Synthetic_Null_Export,
              Variant => Normal_Use);

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type;
   --  Hash function for flow ids. The idea is that a direct mapping the node N
   --  will return the same hash as a magic string mapping to node N.

   function Present (F : Flow_Id) return Boolean
   is (F.Kind /= Null_Value);
   --  Returns True iff F is not null

   function Synthetic (F : Flow_Id) return Boolean
   is (F.Kind = Synthetic_Null_Export);
   --  Returns True iff F is a synthesised Flow_Id

   function Direct_Mapping_Id
     (N       : Node_Or_Entity_Id;
      Variant : Flow_Id_Variant  := Normal_Use;
      Facet   : Variable_Facet_T := Normal_Part)
      return Flow_Id
   with Pre => Present (N);
   --  Create a Flow_Id for the given node or entity

   function Get_Direct_Mapping_Id
     (F : Flow_Id)
      return Node_Id
   with Pre  => F.Kind in Direct_Mapping | Record_Field,
        Post => Present (Get_Direct_Mapping_Id'Result);
   --  Given a direct mapping Flow_Id, return the associated node or entity. In
   --  case of a record field, return the entire variable.

   function Record_Field_Id
     (N : Node_Id)
      return Flow_Id
   with Pre => Present (N) and then Nkind (N) = N_Selected_Component;
   --  Create a Flow_Id for the given record field

   function Add_Component
     (F    : Flow_Id;
      Comp : Entity_Id)
      return Flow_Id
   with Pre  => F.Kind in Direct_Mapping | Record_Field
                  and then
                (Is_Part_Of_Concurrent_Object (Comp)
                   or else
                 Is_Unique_Component (Comp))
                  and then
                F.Facet = Normal_Part,
        Post => Add_Component'Result.Kind = Record_Field;
   --  Returns the same Flow_Id, but accessed with the given component

   function Magic_String_Id
     (S       : Entity_Name;
      Variant : Flow_Id_Variant := Normal_Use)
      return Flow_Id;
   --  Create a Flow_Id for the given magic string.

   function Belongs_To_Concurrent_Type (F : Flow_Id) return Boolean;
   --  @param F is the Flow_Id which will be checked
   --  @return True iff F represents a discriminant, component, or Part_Of
   --     concurrent type

   function Encapsulating_State (F : Flow_Id) return Flow_Id
   with Pre => F.Kind in Direct_Mapping | Record_Field | Magic_String
               and then Is_Constituent (F);
   --  Returns the encapsulating state of F

   function Is_Discriminant (F : Flow_Id) return Boolean
   with Pre => Present (F);
   --  @param F is the Flow_Id which will be checked
   --  @return True iff the given Flow_Id is discriminant (this includes
   --    discriminants for protected types and tasks).

   function Is_Private_Part (F : Flow_Id) return Boolean
   is (F.Kind in Direct_Mapping | Record_Field
         and then F.Facet = Private_Part);
   --  Returns True if the given Flow_Id represents the hidden part of a record
   --  (used when something is private and we don't have visibility).

   function Is_Entire_Variable (F : Flow_Id) return Boolean
   is (case F.Kind is
       when Direct_Mapping => F.Facet = Normal_Part and then
                              Nkind (F.Node) in N_Entity,
       when Synthetic_Null_Export | Magic_String => True,
       when Null_Value | Record_Field            => False);
   --  Returns True iff the given flow id represents an entire variable (or the
   --  magic null export, or a magic string).

   function Is_Extension (F : Flow_Id) return Boolean
   is (F.Kind in Direct_Mapping | Record_Field
         and then F.Facet = Extension_Part);
   --  Returns True if the given Flow_Id represents the extension part of a
   --  record.

   function Is_Record_Tag (F : Flow_Id) return Boolean
   is (F.Kind in Direct_Mapping | Record_Field
         and then F.Facet = The_Tag);
   --  Returns True if the given Flow_Id represents the tag of a classwide type

   function Is_Bound (F : Flow_Id) return Boolean
   is (F.Kind in Direct_Mapping | Record_Field
         and then F.Facet = The_Bounds);
   --  Returns True if the given Flow_Id represents a bound

   function Is_Volatile (F : Flow_Id) return Boolean;
   --  Returns True if the given Flow_Id is volatile in any way

   function Has_Async_Readers (F : Flow_Id) return Boolean
   with Post => (if Has_Async_Readers'Result then Is_Volatile (F));
   --  Checks if F has async readers

   function Has_Async_Writers (F : Flow_Id) return Boolean
   with Post => (if Has_Async_Writers'Result then Is_Volatile (F));
   --  Checks if F has async writers

   function Has_Effective_Reads (F : Flow_Id) return Boolean
   with Post => (if Has_Effective_Reads'Result then Has_Async_Writers (F));
   --  Checks if reads of F are always effective

   function Has_Effective_Writes (F : Flow_Id) return Boolean
   with Post => (if Has_Effective_Writes'Result then Has_Async_Readers (F));
   --  Checks if writes to F are always effective

   function Is_Volatile_For_Reading (F : Flow_Id) return Boolean
   --  Returns True if the given Flow_Id is effectively volatile for reading
   is (Is_Volatile (F)
       and then (Has_Async_Writers (F) or else Has_Effective_Reads (F)));

   function Is_Abstract_State (F : Flow_Id) return Boolean;
   --  Checks if F is an abstract state

   function Is_Constant (F : Flow_Id) return Boolean
   with Pre => Present (F);
   --  Checks if F represents a constant object

   function Is_Constituent (F : Flow_Id) return Boolean;
   --  Checks if F is a constituent of an abstract state

   function Is_Function_Entity (F : Flow_Id) return Boolean;
   --  Checks if F is a function entity (and thus used to capture the
   --  function's return value).

   function Is_Internal (F : Flow_Id) return Boolean
   with Pre => Present (F), Ghost;
   --  Checks if F represents an internal entity

   function Change_Variant (F       : Flow_Id;
                            Variant : Flow_Id_Variant)
                            return Flow_Id
   with Pre => Present (F);
   --  Returns a copy of the given Flow_Id, but with a modified variant

   function Parent_Record (F : Flow_Id) return Flow_Id
   with Pre  => (F.Kind = Record_Field
                   or else
                 (F.Kind = Direct_Mapping and then F.Facet /= Normal_Part))
                  and then
                F.Variant in Initial_Grouping
                           | Initial_Value
                           | Final_Grouping
                           | Final_Value,
        Post => Parent_Record'Result.Kind in Direct_Mapping | Record_Field
                and then Parent_Record'Result.Facet = Normal_Part
                and then Parent_Record'Result.Variant = F.Variant;
   --  Return the parent record for the given record field. If given the
   --  hidden fields of a record, returns the visible part (i.e. clears the
   --  hidden_part flag before moving up the component list). If given a
   --  constituent of a protected object then the protected object is returned.

   function Entire_Variable (F : Flow_Id) return Flow_Id
   with Pre  => Present (F),
        Post => Is_Entire_Variable (Entire_Variable'Result);
   --  Returns the entire variable represented by F

   procedure Sprint_Flow_Id (F : Flow_Id);
   --  Debug procedure to print the given flow id, similar to Sprint_Node

   procedure Print_Flow_Id (F : Flow_Id);
   --  Debug procedure to print the flow id with more information (such as kind
   --  and variant) attached.

   function Flow_Id_To_String
     (F      : Flow_Id;
      Pretty : Boolean := False)
      return String
   with Pre => Is_Easily_Printable (F);
   --  Convert a flow id to a human readable string. This is used mainly
   --  for emitting error messages, where we want entities represented by
   --  Magic_String to be pretty-printed (so Pretty should be True) and for
   --  the graphviz/debug output where we prefer Magic_String to be evident
   --  (so Pretty should be False).

   function Is_Easily_Printable (F : Flow_Id) return Boolean;
   --  Check if F can be printed without resorting to Sprint

   package Flow_Graphs is new Graphs
     (Vertex_Key   => Flow_Id,
      Key_Hash     => Hash,
      Edge_Colours => Edge_Colours,
      Null_Key     => Null_Flow_Id,
      Test_Key     => "=");

   ----------------------------------------------------------------------
   --  Types based on Flow_Id
   ----------------------------------------------------------------------

   package Flow_Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Flow_Id_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Id,
      Element_Type    => Flow_Id_Sets.Set,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => Flow_Id_Sets."=");

   package Flow_Id_Surjection is new Ada.Containers.Hashed_Maps
     (Key_Type        => Flow_Id,
      Element_Type    => Flow_Id,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package Ordered_Flow_Id_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Flow_Id,
      "<"          => "<",
      "="          => "=");

   type Global_Flow_Ids is record
      Proof_Ins : Flow_Id_Sets.Set;
      Inputs    : Flow_Id_Sets.Set;
      Outputs   : Flow_Id_Sets.Set;
   end record;
   pragma Predicate
     (Global_Flow_Ids,
      (for all Proof_In of Proof_Ins =>
          not Inputs.Contains (Proof_In)
            and then
          not Outputs.Contains (Proof_In)));
   --  ??? This predicate is a pragma, because GNAT crashes if it is given as
   --  an aspect [SA23-034].

   function To_Ordered_Flow_Id_Set (S : Flow_Id_Sets.Set)
                                    return Ordered_Flow_Id_Sets.Set;
   --  Convert a hashed flow id set into an ordered flow id set

   function To_Entire_Variables (S : Flow_Id_Sets.Set)
                                 return Flow_Id_Sets.Set
   with Post => (for all X of To_Entire_Variables'Result =>
                   X.Kind /= Record_Field);
   --  Convert a set containing flattened records into a set containing only
   --  entire variables.

   function To_Name (F : Flow_Id) return Entity_Name;
   --  Convert a flow id to an entity name. Any record fields are changed into
   --  entire variables.

   function To_Node_Set (S : Flow_Id_Sets.Set) return Node_Sets.Set
   with Pre => (for all F of S => F.Kind = Direct_Mapping);
   --  Convert a simple Flow_Id set to a node set

   function To_Flow_Id_Set
     (S    : Node_Sets.Set;
      View : Flow_Id_Variant := Normal_Use)
      return Flow_Id_Sets.Set
   with Post => (for all F of To_Flow_Id_Set'Result =>
                   F.Kind = Direct_Mapping);
   --  Convert a node set to a Flow_Id set

   function Change_Variant (FS      : Flow_Id_Sets.Set;
                            Variant : Flow_Id_Variant)
                            return Flow_Id_Sets.Set;
   --  Returns a copy of the given flow id set, but with a modified variant

   ----------------------------------------------------------------------
   --  V_Attributes
   ----------------------------------------------------------------------

   --  If you change this type, please also update Print_Graph_Vertex in Flow

   type Pretty_Print_Kind_T is (Pretty_Print_Null,
                                Pretty_Print_DIC,
                                Pretty_Print_Package,
                                Pretty_Print_Folded_Function_Check,
                                Pretty_Print_Loop_Init,
                                Pretty_Print_Record_Field,
                                Pretty_Print_Entry_Barrier,
                                Pretty_Print_Borrow);

   type V_Attributes is record
      Is_Null_Node                 : Boolean;
      --  Set for auxiliary nodes which can be removed, such as early returns
      --  or null statements.

      Is_Program_Node              : Boolean;
      --  Set for all vertices which both
      --     - trace directly to an element in the AST,
      --     - they are constructs which could be ineffective
      --
      --  Setting this attribute enables the following analyses which would not
      --  normally be performed:
      --     * ineffective_statements
      --
      --  It should be noted that most vertices we construct will have this set
      --  to true.

      In_Nested_Package            : Boolean;
      --  True for vertices created for constructs in nested packages

      Is_Exceptional_Branch        : Boolean;
      --  True for nodes which lead *into* an exceptional path (see below), but
      --  are not part of the path itself.

      Is_Exceptional_Path          : Boolean;
      --  True for all nodes on exceptional execution paths, i.e. paths leading
      --  to raise statements, statically false assertions and calls to
      --  subprograms with pragma No_Return. We tend to exclude these from
      --  analysis and sanity checking.

      Is_Assertion                 : Boolean;
      --  True if this vertex represents an assertion expression

      Is_Package_Initialization    : Boolean;
      --  True if this vertex represents a package initialization

      Is_Default_Init              : Boolean;
      --  True if this vertex represents a default initialization

      Is_Loop_Entry                : Boolean;
      --  True if this vertex represents a loop entry assignment. For each
      --  variable where we use 'Loop_Entry we have one of these at the top of
      --  the actual loop.

      Is_Initialized               : Boolean;
      --  True if an initial value is either imported (in or in out) or
      --  otherwise initialized.

      Is_Function_Return           : Boolean;
      --  True if this vertex models the returned value of a function

      Is_Global                    : Boolean;
      --  True if the imported or exported variable is a global

      Is_Import                    : Boolean;
      --  True if the given initial value is a parameter or global of the
      --  analysed subprogram.

      Is_Export                    : Boolean;
      --  True if the given final-use variable is actually relevant to a
      --  subprogram's exports (out parameter or global out).

      Mode                         : Param_Mode;
      --  Set for initial and final use vertices which are parameters or
      --  globals.

      Is_Package_State             : Boolean;
      --  True if the given variable is part of a package' state

      Is_Constant                  : Boolean;
      --  True if this value may not be updated

      Is_Callsite                  : Boolean;
      --  True if the vertex represents a subprogram call

      Is_Parameter                 : Boolean;
      --  True if this vertex models an argument to a procedure call

      Is_Discr_Or_Bounds_Parameter : Boolean;
      --  If true this only captures the discriminants or bounds of a parameter

      Is_Global_Parameter          : Boolean;
      --  True if this vertex models a global for a procedure or function call

      Is_Implicit_Parameter        : Boolean;
      --  True if this vertex models an implicit formal parameter of a
      --  subprogram.

      Is_Neverending               : Boolean;
      --  True if this vertex models a loop that is detected as potentially
      --  nonreturning.

      Execution                    : Execution_Kind_T;
      --  Determines how we should treat edges from this vertex. Most nodes
      --  will have Normal_Execution set here.

      Perform_IPFA                 : Boolean;
      --  True if the dependencies for this callsite should be filled in using
      --  interprocedural flow analysis.

      Call_Vertex                  : Flow_Id;
      --  Used to identify which vertex a parameter vertex belongs to.

      Parameter_Actual             : Flow_Id;
      Parameter_Formal             : Flow_Id;
      --  For nodes where Is_Parameter is true, this keeps track of which
      --  parameter this is. This is also quite useful for pretty-printing.
      --  For nodes with Is_Global_Parameter only Parameter_Formal is set.

      Default_Init_Var             : Flow_Id;
      Default_Init_Val             : Node_Id;
      --  For default initializations (Is_Default_Init) this pair records which
      --  variable has a default value (Var) and what it is (Val).

      Variables_Defined            : Flow_Id_Sets.Set;
      Variables_Used               : Flow_Id_Sets.Set;
      Variables_Read               : Flow_Id_Sets.Set;
      --  For producing the DDG

      Variables_Explicitly_Used    : Flow_Id_Sets.Set;
      --  Similar to Variables_Used, but does not include the implicit
      --  self-dependency for partial record and array updates.

      Volatiles_Read               : Flow_Id_Sets.Set;
      Volatiles_Written            : Flow_Id_Sets.Set;
      --  Again, for producing the DDG. These are implied updates due to reads
      --  of volatiles where reads are effective.

      Subprograms_Called           : Node_Sets.Set;
      --  The set of all subprograms (functions and procedures) called; think
      --  of this as Variables_Used, but for subprogram calls.

      Loops                        : Node_Sets.Set;
      --  Which loops are we a member of (identified by loop name/label). For
      --  loop stability analysis.

      Record_RHS                   : Flow_Graphs.Vertex_Id;
      --  Vertex with a variables used on the RHS of a record assignment

      Error_Location               : Node_Or_Entity_Id;
      --  If we have an error involving this vertex, raise it here

      Aux_Node                     : Node_Or_Entity_Id;
      --  The meaning of this depends on the kind of vertex these attributes
      --  are attached to.
      --
      --     * E_Return_Statement : for the implicit extended return
      --       returns this keeps track of the actual variable we return.

      Pretty_Print_Kind            : Pretty_Print_Kind_T;
      --  Some extra information which we use when deciding how to pretty print
      --  the vertex in --flow-debug mode.
   end record;

   Null_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node                    => False,
                   In_Nested_Package               => False,
                   Is_Program_Node                 => False,
                   Is_Exceptional_Branch           => False,
                   Is_Exceptional_Path             => False,
                   Is_Assertion                    => False,
                   Is_Package_Initialization       => False,
                   Is_Default_Init                 => False,
                   Is_Loop_Entry                   => False,
                   Is_Initialized                  => False,
                   Is_Function_Return              => False,
                   Is_Global                       => False,
                   Is_Import                       => False,
                   Is_Export                       => False,
                   Mode                            => Mode_Invalid,
                   Is_Package_State                => False,
                   Is_Constant                     => False,
                   Is_Callsite                     => False,
                   Is_Parameter                    => False,
                   Is_Discr_Or_Bounds_Parameter    => False,
                   Is_Global_Parameter             => False,
                   Is_Implicit_Parameter           => False,
                   Is_Neverending                  => False,
                   Execution                       => Normal_Execution,
                   Perform_IPFA                    => False,
                   Call_Vertex                     => Null_Flow_Id,
                   Parameter_Actual                => Null_Flow_Id,
                   Parameter_Formal                => Null_Flow_Id,
                   Default_Init_Var                => Null_Flow_Id,
                   Default_Init_Val                => Empty,
                   Variables_Defined               => Flow_Id_Sets.Empty_Set,
                   Variables_Used                  => Flow_Id_Sets.Empty_Set,
                   Variables_Read                  => Flow_Id_Sets.Empty_Set,
                   Variables_Explicitly_Used       => Flow_Id_Sets.Empty_Set,
                   Volatiles_Read                  => Flow_Id_Sets.Empty_Set,
                   Volatiles_Written               => Flow_Id_Sets.Empty_Set,
                   Subprograms_Called              => Node_Sets.Empty_Set,
                   Loops                           => Node_Sets.Empty_Set,
                   Record_RHS                      => Flow_Graphs.Null_Vertex,
                   Error_Location                  => Empty,
                   Aux_Node                        => Empty,
                   Pretty_Print_Kind               => Pretty_Print_Null);

   Null_Node_Attributes : constant V_Attributes :=
     (Null_Attributes with delta Is_Null_Node    => True,
                                 Is_Program_Node => True);

   type Reference_Kind is (Inputs, Proof_Ins, Null_Deps);
   --  Modes for queries about variables referenced in a given expression. For
   --  example, when quering a call to function annotated like this:
   --
   --    function F return Integer
   --    with Global  => (Input => (A, B), Proof_In => C),
   --         Depends => (F'Result => A,
   --                     null     => B);
   --
   --  when routine Get_Variables is called it will return the following:
   --
   --    Inputs    => {A}
   --    Proof_Ins => {C}
   --    Null_Deps => {B}
   --
   --  Results in modes Inputs and Proof_Ins are come from straightforward
   --  references to variables; results in mode Null_Deps come from calls to
   --  subprograms with "null => ..." dependency clauses, 'Update expressions,
   --  delay statements, etc.

end Flow_Types;
