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
with Ada.Containers.Hashed_Sets;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Vectors;

with Atree; use Atree;
with Einfo; use Einfo;
with Types; use Types;

with Gnat2Why.Nodes;        use Gnat2Why.Nodes;
--  Node_Sets and Node_Hash

with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;
--  Entity_Name

with Graph;

package Flow is

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

      In_View,
      Out_View
      --  For the procedure call parameter vertices.
   );

   subtype Initial_Or_Final_Variant is Flow_Id_Variant
     range Initial_Value .. Final_Value;

   type Flow_Id is record
      Kind    : Flow_Id_Kind;
      Variant : Flow_Id_Variant;
      Node_A  : Node_Id;
      Node_B  : Node_Id;
      E_Name  : Entity_Name;
   end record;

   function "=" (Left, Right : Flow_Id) return Boolean;

   Null_Flow_Id : constant Flow_Id := Flow_Id'(Kind    => Null_Value,
                                               Variant => Normal_Use,
                                               Node_A  => Empty,
                                               Node_B  => Empty,
                                               E_Name  => Null_Entity_Name);

   function Hash (N : Flow_Id) return Ada.Containers.Hash_Type;

   procedure Sprint_Flow_Id (F : Flow_Id);

   function Direct_Mapping_Id (N       : Node_Id;
                               Variant : Flow_Id_Variant := Normal_Use)
                               return Flow_Id
   is (Flow_Id'(Kind    => Direct_Mapping,
                Variant => Variant,
                Node_A  => N,
                Node_B  => Empty,
                E_Name  => Null_Entity_Name));

   function Get_Direct_Mapping_Id
     (F : Flow_Id)
      return Node_Id
      with Pre => (F.Kind = Direct_Mapping);

   package Flow_Id_Sets is new Ada.Containers.Hashed_Sets
     (Element_Type        => Flow_Id,
      Hash                => Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

   type V_Attributes is record
      Is_Null_Node      : Boolean;
      --  Set for auxiliary nodes which can be removed, such as early
      --  returns or null statements.

      Is_Program_Node   : Boolean;
      --  Set for all vertices which trace directly to an element in
      --  the AST.

      Is_Initialised    : Boolean;
      --  True if an initial value is either imported (in or in out)
      --  or otherwise initialised.

      Is_Loop_Parameter : Boolean;
      --  True for loop parameters so they can be ignored in
      --  ineffective-import analysis.

      Is_Export         : Boolean;
      --  True if the given final-use variable is actually relevant to
      --  a subprogram's exports (out parameter or global out).

      Is_Callsite       : Boolean;
      --  True if the vertex represents a subprogram call.

      Is_Parameter      : Boolean;
      --  True if this vertex models an argument to a procedure call.

      Perform_IPFA      : Boolean;
      --  True if the dependencies for this callsite should be filled
      --  in using interprocedural flow analysis.

      Call_Vertex       : Flow_Id;
      --  Used to identify which vertex a parameter vertex belongs to.

      Parameter_Actual  : Flow_Id;
      Parameter_Formal  : Flow_Id;
      --  For nodes where Is_Parameter is true, this keeps track of
      --  which parameter this is. This is also quite useful for
      --  pretty-printing.

      Variables_Defined : Flow_Id_Sets.Set;
      Variables_Used    : Flow_Id_Sets.Set;
      --  For producing the DDG.

      Loops             : Node_Sets.Set;
      --  Which loops are we a member of (identified by loop
      --  name/label). For loop stability analysis.
   end record;

   Null_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node      => False,
                   Is_Program_Node   => False,
                   Is_Initialised    => False,
                   Is_Loop_Parameter => False,
                   Is_Export         => False,
                   Is_Callsite       => False,
                   Is_Parameter      => False,
                   Perform_IPFA      => False,
                   Call_Vertex       => Null_Flow_Id,
                   Parameter_Actual  => Null_Flow_Id,
                   Parameter_Formal  => Null_Flow_Id,
                   Variables_Defined => Flow_Id_Sets.Empty_Set,
                   Variables_Used    => Flow_Id_Sets.Empty_Set,
                   Loops             => Node_Sets.Empty_Set);

   Null_Node_Attributes : constant V_Attributes :=
     V_Attributes'(Is_Null_Node      => True,
                   Is_Program_Node   => True,
                   Is_Initialised    => False,
                   Is_Loop_Parameter => False,
                   Is_Export         => False,
                   Is_Callsite       => False,
                   Is_Parameter      => False,
                   Perform_IPFA      => False,
                   Call_Vertex       => Null_Flow_Id,
                   Parameter_Actual  => Null_Flow_Id,
                   Parameter_Formal  => Null_Flow_Id,
                   Variables_Defined => Flow_Id_Sets.Empty_Set,
                   Variables_Used    => Flow_Id_Sets.Empty_Set,
                   Loops             => Node_Sets.Empty_Set);

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

   type Flow_Analysis_Graphs is record
      Subprogram   : Entity_Id;
      Start_Vertex : Flow_Graphs.Vertex_Id;
      End_Vertex   : Flow_Graphs.Vertex_Id;
      CFG          : Flow_Graphs.T;
      DDG          : Flow_Graphs.T;
      CDG          : Flow_Graphs.T;
      TDG          : Flow_Graphs.T;
      PDG          : Flow_Graphs.T;
      Vars         : Flow_Id_Sets.Set;
      Loops        : Node_Sets.Set;
   end record;

   function Loop_Parameter_From_Loop (E : Entity_Id) return Entity_Id
     with Pre  => Ekind (E) = E_Loop,
          Post => Loop_Parameter_From_Loop'Result = Empty or else
                  Ekind (Loop_Parameter_From_Loop'Result) = E_Loop_Parameter;
   --  Given a loop label, returns the identifier of the loop
   --  parameter or Empty.

   procedure Print_Graph
     (Filename     : String;
      G            : Flow_Graphs.T;
      Start_Vertex : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      End_Vertex   : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex);
   --  Write a dot and pdf file for the given graph.

   procedure Flow_Analyse_Entity (E : Entity_Id);
   --  Flow analyse the given entity. This subprogram does nothing for
   --  entities without a body and not in SPARK 2014.

end Flow;
