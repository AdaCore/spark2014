------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . S L I C E                            --
--                                                                          --
--                                 B o d y                                  --
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

with Why;

package body Flow.Slice is

   ----------------------------------------------------------------------
   --  Local procedures for local subprograms
   ----------------------------------------------------------------------

   function Internal_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id;
      IPFA    : Boolean)
      return Vertex_Sets.Set;
   --  Helper function to compute the dependencies for a single
   --  vertex.

   -------------------------
   -- Internal_Dependency --
   -------------------------

   function Internal_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id;
      IPFA    : Boolean)
      return Vertex_Sets.Set
   is
      Deps : Vertex_Sets.Set := Vertex_Sets.Empty_Set;

      procedure Visitor
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction);
      --  If the visited vertex is an in vertex or a procedure
      --  parameter vertex, we add it to the set of things we depend
      --  on.

      procedure Visitor
        (V  : Flow_Graphs.Vertex_Id;
         TV : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         F : constant Flow_Id := FA.PDG.Get_Key (V);
      begin
         case F.Variant is
            when Initial_Value | Final_Value =>
               Deps.Include (V);
            when In_View | Out_View =>
               if IPFA then
                  Deps.Include (V);
               end if;
            when Initial_Grouping | Final_Grouping =>
               null;
            when Normal_Use =>
               null;
         end case;
         TV := Flow_Graphs.Continue;
      end Visitor;

   begin
      Flow_Graphs.DFS (G             => FA.PDG,
                       Start         => V_Final,
                       Include_Start => False,
                       Visitor       => Visitor'Access,
                       Reversed      => True);
      return Deps;
   end Internal_Dependency;

   ----------------------------------------------------------------------
   --  Package subprograms
   ----------------------------------------------------------------------

   ----------------
   -- Dependency --
   ----------------

   function Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Flow_Id_Sets.Set
   is
      Tmp  : constant Vertex_Sets.Set :=
        Internal_Dependency (FA      => FA,
                             V_Final => V_Final,
                             IPFA    => False);

      Deps : Flow_Id_Sets.Set := Flow_Id_Sets.Empty_Set;
   begin
      for V of Tmp loop
         Deps.Include (Change_Variant (FA.PDG.Get_Key (V), Normal_Use));
      end loop;
      return Deps;
   end Dependency;

   ---------------------
   -- IPFA_Dependency --
   ---------------------

   function IPFA_Dependency
     (FA      : Flow_Analysis_Graphs;
      V_Final : Flow_Graphs.Vertex_Id)
      return Vertex_Sets.Set
   is
   begin
      return Internal_Dependency (FA      => FA,
                                  V_Final => V_Final,
                                  IPFA    => True);
   end IPFA_Dependency;

   ---------------------------------
   -- Compute_Dependency_Relation --
   ---------------------------------

   function Compute_Dependency_Relation
     (FA : Flow_Analysis_Graphs)
      return Dependency_Maps.Map
   is

      function Flow_Equivalent (F : Flow_Id) return Flow_Id
        with Post => Flow_Equivalent'Result.Variant = Normal_Use;
      --  Given a flow id, return the view the dependency relation
      --  cares about. For example R.X.Y will yield R, but
      --  R.Discriminant will yield R.Discriminant.

      function Flow_Equivalent (F : Flow_Id) return Flow_Id
      is
      begin
         case F.Kind is
            when Direct_Mapping | Magic_String =>
               return Change_Variant (F, Normal_Use);

            when Record_Field =>
               return Change_Variant (Entire_Variable (F), Normal_Use);

            when Null_Value =>
               raise Why.Unexpected_Node;
         end case;
      end Flow_Equivalent;

      In_Vertices   : Vertex_Sets.Set     := Vertex_Sets.Empty_Set;
      Out_Vertices  : Vertex_Sets.Set     := Vertex_Sets.Empty_Set;

      Unused_Inputs : Flow_Id_Sets.Set    := Flow_Id_Sets.Empty_Set;

      DM            : Dependency_Maps.Map := Dependency_Maps.Empty_Map;

      use type Vertex_Sets.Set;

   begin

      --  Determine all out vertices.

      for V_Final of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Final : constant Flow_Id      := FA.PDG.Get_Key (V_Final);
            Attr    : constant V_Attributes :=
              FA.PDG.Get_Attributes (V_Final);
         begin
            if F_Final.Variant = Final_Value
              and then Attr.Is_Export
            then
               Out_Vertices.Include (V_Final);
            end if;
         end;
      end loop;

      --  Determine all input vertices.

      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            F_Initial : constant Flow_Id      := FA.PDG.Get_Key (V_Initial);
            Attr      : constant V_Attributes :=
              FA.PDG.Get_Attributes (V_Initial);
         begin
            if F_Initial.Variant = Initial_Value
              and then Attr.Is_Import
            then
               In_Vertices.Include (V_Initial);
               Unused_Inputs.Include (Flow_Equivalent (F_Initial));
            end if;
         end;
      end loop;

      --  Determine dependencies.

      for V_Out of Out_Vertices loop
         declare
            F_In  : Flow_Id;
            F_Out : constant Flow_Id :=
              Flow_Equivalent (FA.PDG.Get_Key (V_Out));

            --  Compute dependencies (and filter out local variables).
            Deps : constant Vertex_Sets.Set :=
              Internal_Dependency (FA      => FA,
                                   V_Final => V_Out,
                                   IPFA    => False)
              and In_Vertices;
         begin
            if not DM.Contains (F_Out) then
               DM.Include (F_Out, Flow_Id_Sets.Empty_Set);
            end if;

            for V_In of Deps loop
               F_In := Flow_Equivalent (FA.PDG.Get_Key (V_In));

               DM (F_Out).Include (F_In);
               Unused_Inputs.Exclude (F_In);
            end loop;
         end;
      end loop;

      DM.Include (Null_Flow_Id, Unused_Inputs);

      return DM;

   end Compute_Dependency_Relation;

end Flow.Slice;
