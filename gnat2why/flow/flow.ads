------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                 F L O W                                  --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
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

with Ada.Containers;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Ordered_Sets;
with Ada.Containers.Vectors;

with Atree; use Atree;
with Einfo; use Einfo;
with Sinfo; use Sinfo;
with Types; use Types;

with Gnat2Why.Nodes;         use Gnat2Why.Nodes;
--  Node_Sets and Node_Hash

with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
--  Entity_Name

with Graph;

package Flow is

   type Global_Modes is (Global_Mode_In,
                         Global_Mode_Proof,
                         Global_Mode_In_Out,
                         Global_Mode_Out);

   subtype In_Global_Modes is Global_Modes
     range Global_Mode_In .. Global_Mode_Proof;

   subtype Initialised_Global_Modes is Global_Modes
     range Global_Mode_In .. Global_Mode_In_Out;

   subtype Exported_Global_Modes is Global_Modes
     range Global_Mode_In_Out .. Global_Mode_Out;

   type Edge_Colours is (EC_Default, EC_DDG, EC_TD);

   type Flow_Id_Kind is (Null_Value,
                         Direct_Mapping,
                         Record_Field,
                         Magic_String);

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

   package Entity_Lists is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Entity_Id);

   type Flow_Id is record
      Kind      : Flow_Id_Kind;
      Variant   : Flow_Id_Variant;

      Node      : Node_Or_Entity_Id;
      --  For Kind = Direct_Mapping | Record_Field

      Name      : Entity_Name;
      --  For Kind = Magic_String

      Component : Entity_Lists.Vector;
      --  For Kind = Record_Field
   end record;

   function "=" (Left, Right : Flow_Id) return Boolean;
   --  Equality function for flow id.

   function "<" (Left, Right : Flow_Id) return Boolean;
   --  Ordering for flow id.

   function Lexicographic_Entity_Order (Left, Right : Entity_Id)
                                        return Boolean;
   --  Ordering for normal nodes.

   Null_Flow_Id : constant Flow_Id :=
     Flow_Id'(Kind      => Null_Value,
              Variant   => Normal_Use,
              Node      => Empty,
              Name      => Null_Entity_Name,
              Component => Entity_Lists.Empty_Vector);

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type;
   --  Hash function for flow id's. The idea is that a direct mapping
   --  to node N will return the same hash as a magic string mapping
   --  to node N.

   procedure Sprint_Flow_Id (F : Flow_Id);
   --  Debug procedure to print the given flow id, similar to
   --  Sprint_Node.

   procedure Print_Flow_Id (F : Flow_Id);
   --  Debug procedure to print the flow id with more information
   --  (such as kind and variant) attached.

   function Flow_Id_To_String (F : Flow_Id) return String;
   --  Convert a flow id to a human readable string. This is used for
   --  emitting error messages.

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

   package Flow_Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   package Ordered_Flow_Id_Sets is new Ada.Containers.Ordered_Sets
     (Element_Type => Flow_Id,
      "<"          => "<",
      "="          => "=");

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

   function To_Ordered_Flow_Id_Set (S : Flow_Id_Sets.Set)
                                    return Ordered_Flow_Id_Sets.Set;
   --  Convert a hashed flow id set into an ordered node set.

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

      Is_Loop_Entry       : Boolean;
      --  True if this vertex represents a loop entry assignment. For
      --  each variable where we use 'Loop_Entry we have one of these
      --  at the top of the actual loop.

      Is_Initialised      : Boolean;
      --  True if an initial value is either imported (in or in out)
      --  or otherwise initialised.

      Is_Function_Return  : Boolean;
      --  True if this vertex models the returned value of a function.

      Is_Global           : Boolean;
      --  True if the imported or exported variable is a global.

      Is_Loop_Parameter   : Boolean;
      --  True for loop parameters so they can be ignored in
      --  ineffective-import analysis.

      Is_Export           : Boolean;
      --  True if the given final-use variable is actually relevant to
      --  a subprogram's exports (out parameter or global out).

      Is_Constant         : Boolean;
      --  True if this value may not be updated.

      Is_Callsite         : Boolean;
      --  True if the vertex represents a subprogram call.

      Is_Parameter        : Boolean;
      --  True if this vertex models an argument to a procedure call.

      Is_Global_Parameter : Boolean;
      --  True if this vertex models a global for a procedure or
      --  function call.

      Perform_IPFA        : Boolean;
      --  True if the dependencies for this callsite should be filled
      --  in using interprocedural flow analysis.

      Call_Vertex         : Flow_Id;
      --  Used to identify which vertex a parameter vertex belongs to.

      Parameter_Actual    : Flow_Id;
      Parameter_Formal    : Flow_Id;
      --  For nodes where Is_Parameter is true, this keeps track of
      --  which parameter this is. This is also quite useful for
      --  pretty-printing.

      Variables_Defined   : Flow_Id_Sets.Set;
      Variables_Used      : Flow_Id_Sets.Set;
      --  For producing the DDG.

      Loops               : Node_Sets.Set;
      --  Which loops are we a member of (identified by loop
      --  name/label). For loop stability analysis.

      Error_Location      : Node_Or_Entity_Id;
      --  If we have an error involving this vertex, raise it here.
   end record;
   pragma Pack (V_Attributes);

   Null_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node        => False,
                   Is_Program_Node     => False,
                   Is_Precondition     => False,
                   Is_Loop_Entry       => False,
                   Is_Initialised      => False,
                   Is_Function_Return  => False,
                   Is_Global           => False,
                   Is_Loop_Parameter   => False,
                   Is_Export           => False,
                   Is_Constant         => False,
                   Is_Callsite         => False,
                   Is_Parameter        => False,
                   Is_Global_Parameter => False,
                   Perform_IPFA        => False,
                   Call_Vertex         => Null_Flow_Id,
                   Parameter_Actual    => Null_Flow_Id,
                   Parameter_Formal    => Null_Flow_Id,
                   Variables_Defined   => Flow_Id_Sets.Empty_Set,
                   Variables_Used      => Flow_Id_Sets.Empty_Set,
                   Loops               => Node_Sets.Empty_Set,
                   Error_Location      => Empty);

   Null_Node_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node        => True,
                   Is_Program_Node     => True,
                   Is_Precondition     => False,
                   Is_Loop_Entry       => False,
                   Is_Initialised      => False,
                   Is_Function_Return  => False,
                   Is_Global           => False,
                   Is_Loop_Parameter   => False,
                   Is_Export           => False,
                   Is_Constant         => False,
                   Is_Callsite         => False,
                   Is_Parameter        => False,
                   Is_Global_Parameter => False,
                   Perform_IPFA        => False,
                   Call_Vertex         => Null_Flow_Id,
                   Parameter_Actual    => Null_Flow_Id,
                   Parameter_Formal    => Null_Flow_Id,
                   Variables_Defined   => Flow_Id_Sets.Empty_Set,
                   Variables_Used      => Flow_Id_Sets.Empty_Set,
                   Loops               => Node_Sets.Empty_Set,
                   Error_Location      => Empty);

   package Flow_Graphs is new Graph
     (Vertex_Key        => Flow_Id,
      Vertex_Attributes => V_Attributes,
      Edge_Colours      => Edge_Colours,
      Null_Key          => Null_Flow_Id,
      Test_Key          => "=");

   package Node_To_Vertex_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Flow_Graphs.Vertex_Id,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Flow_Graphs."=");

   package Vertex_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Graphs.Vertex_Id,
      Hash                => Flow_Graphs.Vertex_Hash,
      Equivalent_Elements => Flow_Graphs."=",
      "="                 => Flow_Graphs."=");

   package Vertex_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Positive,
      Element_Type => Flow_Graphs.Vertex_Id,
      "="          => Flow_Graphs."=");

   package Magic_String_To_Node_Sets is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Node_Sets.Set,
      Hash            => Name_Hash,
      Equivalent_Keys => Name_Equal,
      "="             => Node_Sets."=");

   type Flow_Analysis_Graphs is record
      Subprogram       : Entity_Id;
      --  The entity of the analysed subprogram.

      Start_Vertex     : Flow_Graphs.Vertex_Id;
      End_Vertex       : Flow_Graphs.Vertex_Id;
      --  The start and end vertices in the graphs.

      CFG              : Flow_Graphs.T;
      DDG              : Flow_Graphs.T;
      CDG              : Flow_Graphs.T;
      TDG              : Flow_Graphs.T;
      PDG              : Flow_Graphs.T;
      --  The graphs.

      All_Vars         : Flow_Id_Sets.Set;
      --  A set of all variables used.

      Loops            : Node_Sets.Set;
      --  A set of all loops (identified by label).

      Magic_Source     : Magic_String_To_Node_Sets.Map;
      --  A mapping of any magic string to entities of the
      --  subprogram(s) they originate from. We need this to print
      --  more helpful error messages.

      Aliasing_Present : Boolean;
      --  True if this subprogram introduces (bad)
      --  aliasing. Subsequent analysis is then meaningless.
   end record;

   package Analysis_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Flow_Analysis_Graphs,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package Dependency_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Node_Sets.Set,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Node_Sets."=");

   function Loop_Parameter_From_Loop (E : Entity_Id) return Entity_Id
     with Pre  => Ekind (E) = E_Loop,
          Post => not Present (Loop_Parameter_From_Loop'Result) or else
                  Ekind (Loop_Parameter_From_Loop'Result) = E_Loop_Parameter;
   --  Given a loop label, returns the identifier of the loop
   --  parameter or Empty.

   procedure Get_Globals (Subprogram : Entity_Id;
                          Reads      : out Flow_Id_Sets.Set;
                          Writes     : out Flow_Id_Sets.Set)
   with Pre  => Ekind (Subprogram) in E_Procedure | E_Function,
        Post => (for all G of Reads  => G.Variant = In_View) and
                (for all G of Writes => G.Variant = Out_View);
   --  Given a subprogram call, work out globals from the provided
   --  aspect or the computed globals. The sets returned will contain
   --  Flow_Id with the variant set to Global_In_View and
   --  Global_Out_View.

   function Has_Depends (Subprogram : Entity_Id) return Boolean
   with Pre => Ekind (Subprogram) in E_Procedure | E_Function;
   --  Return true if the given subprogram has been annotated with a
   --  dependency relation.

   procedure Get_Depends (Subprogram : Entity_Id;
                          Depends    : out Dependency_Maps.Map)
   with Pre  => Ekind (Subprogram) in E_Procedure | E_Function and
                Has_Depends (Subprogram),
        Post => (for all C in Depends.Iterate =>
                   Present (Dependency_Maps.Key (C)) and
                   (for all D of Dependency_Maps.Element (C) =>
                      Present (D)));
   --  Return the dependency relation of the given subprogram. The
   --  dependency relation is represented as a map from entities to
   --  sets of entities.
   --
   --  For example (X, Y) =>* Z would be represented as:
   --     x -> {x, z}
   --     y -> {y, z}
   --
   --  This procedure can deal with all forms the depends
   --  annotation. For each item in the dependency annotation, the LHS
   --  and RHS can be any of the following:
   --     * (x, y, z)     (an aggregate)
   --     * x             (a variable)
   --     * null          (keyword null)
   --  One final form which is supported is the null dependency.
   --
   --  The * shorthand to mean "itself" is expanded away by the
   --  front-end and this procedure does not have to deal with it.

   procedure Print_Graph
     (Filename     : String;
      G            : Flow_Graphs.T;
      Start_Vertex : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      End_Vertex   : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
   --  Write a dot and pdf file for the given graph.

   procedure Flow_Analyse_CUnit;
   --  Flow analyses the current compilation unit

end Flow;
