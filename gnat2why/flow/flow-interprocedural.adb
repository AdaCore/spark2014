------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . I N T E R P R O C E D U R A L                  --
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

with Sem_Util; use Sem_Util;

with Why;

package body Flow.Interprocedural is

   use type Flow_Graphs.Vertex_Id;

   procedure Add_Simple_Procedure_Dependency
     (FA : in out Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id);
   --  Add dependencies for a simple procedure call where we cannot
   --  perform IPFA.

   function Find_Parameter_Vertex (CDG       : Flow_Graphs.T;
                                   Callsite  : Flow_Graphs.Vertex_Id;
                                   Parameter : Flow_Id)
                                   return Flow_Graphs.Vertex_Id;
   --  Search for the relevant parameter vertex for a given call.

   function Find_Parameter_Vertex (CDG       : Flow_Graphs.T;
                                   Callsite  : Flow_Graphs.Vertex_Id;
                                   Parameter : Flow_Id)
                                   return Flow_Graphs.Vertex_Id is
   begin
      for V of CDG.Get_Collection (Callsite, Flow_Graphs.Out_Neighbours) loop
         declare
            F : constant Flow_Id      := CDG.Get_Key (V);
            A : constant V_Attributes := CDG.Get_Attributes (V);
         begin
            if A.Is_Parameter then
               --  Parameters *must* be using direct mapping for both
               --  the actual and formal.
               pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
               pragma Assert (F.Kind = Direct_Mapping);
               if Parameter.Kind = Direct_Mapping and then
                 Parameter.Variant = F.Variant and then
                 Get_Direct_Mapping_Id (Parameter) =
                 Get_Direct_Mapping_Id (A.Parameter_Formal) then
                  return V;
               end if;

            elsif A.Is_Global_Parameter then
               --  Globals can be direct mappings or magic strings,
               --  but in either case the parameter and the formal
               --  will always match in kind.
               case A.Parameter_Formal.Kind is
                  when Direct_Mapping =>
                     if Parameter.Kind = Direct_Mapping and then
                       A.Parameter_Formal.Variant = Parameter.Variant and then
                       Get_Direct_Mapping_Id (Parameter) =
                       Get_Direct_Mapping_Id (A.Parameter_Formal) then
                        return V;
                     end if;
                  when Magic_String =>
                     if Parameter.Kind = Magic_String and then
                       A.Parameter_Formal.Variant = Parameter.Variant and then
                       Parameter.Name.all = A.Parameter_Formal.Name.all then
                        return V;
                     end if;
                  when others =>
                     raise Program_Error;
               end case;

            else
               --  We have a parameter which is neither a parameter or
               --  a global, i.e. we have messed up in the graph
               --  construction.
               raise Program_Error;
            end if;
         end;
      end loop;

      --  We have looked for a vertex which doesn't exist, which means
      --  the graph is broken.
      Print_Flow_Id (Parameter);
      raise Program_Error;
   end Find_Parameter_Vertex;

   procedure Add_Simple_Procedure_Dependency
     (FA : in out Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id)
   is
      N : constant Node_Id := Get_Direct_Mapping_Id (FA.CFG.Get_Key (V));
      pragma Assert (Nkind (N) = N_Procedure_Call_Statement);

      A : constant V_Attributes := FA.CFG.Get_Attributes (V);
      pragma Assert (A.Is_Callsite);
      pragma Assert (not A.Perform_IPFA);

      Called_Procedure : constant Entity_Id := Entity (Name (N));

      procedure Add_TD_Edge (A, B : Entity_Id);
      --  Add a parameter dependency edge from the input A to the
      --  output B.

      procedure Add_TD_Edge (A, B : Entity_Id) is
         V_A, V_B : Flow_Graphs.Vertex_Id;
      begin
         V_A := Find_Parameter_Vertex
           (FA.CDG,
            V,
            Direct_Mapping_Id (Unique_Entity (A), In_View));

         V_B := Find_Parameter_Vertex
           (FA.CDG,
            V,
            Direct_Mapping_Id (Unique_Entity (B), Out_View));

         FA.TDG.Add_Edge (V_A, V_B, EC_TD);
      end Add_TD_Edge;

   begin
      if Has_Depends (Called_Procedure) then
         --  We have a dependency aspect, so we should use it.
         declare
            Deps : Dependency_Maps.Map;
         begin
            Get_Depends (Called_Procedure, Deps);
            for C in Deps.Iterate loop
               declare
                  Output : constant Entity_Id     := Dependency_Maps.Key (C);
                  Inputs : constant Node_Sets.Set :=
                    Dependency_Maps.Element (C);
               begin
                  for Input of Inputs loop
                     Add_TD_Edge (Input, Output);
                  end loop;
               end;
            end loop;
         end;

      else
         --  We do not have a dependency aspect, so we will make up
         --  one (all outputs depend on all inputs).
         declare
            Inputs  : Flow_Id_Sets.Set;
            Outputs : Flow_Id_Sets.Set;
            E       : Entity_Id;
         begin
            --  Collect all the globals first.
            Get_Globals (Subprogram => Called_Procedure,
                         Reads      => Inputs,
                         Writes     => Outputs);

            --  Add parameters.
            E := First_Formal (Called_Procedure);
            while E /= Empty loop
               case Ekind (E) is
                  when E_In_Parameter =>
                     Inputs.Insert (Direct_Mapping_Id (Unique_Entity (E),
                                                       In_View));

                  when E_In_Out_Parameter =>
                     Inputs.Insert (Direct_Mapping_Id (Unique_Entity (E),
                                                       In_View));
                     Outputs.Insert (Direct_Mapping_Id (Unique_Entity (E),
                                                        Out_View));

                  when E_Out_Parameter =>
                     Outputs.Insert (Direct_Mapping_Id (Unique_Entity (E),
                                                        Out_View));

                  when others =>
                     raise Why.Not_Implemented;
               end case;
               E := Next_Formal (E);
            end loop;

            --  Each output depends on all inputs.
            for Input of Inputs loop
               for Output of Outputs loop
                  FA.TDG.Add_Edge (Find_Parameter_Vertex (FA.CDG, V, Input),
                                   Find_Parameter_Vertex (FA.CDG, V, Output),
                                   EC_TD);
               end loop;
            end loop;
         end;
      end if;
   end Add_Simple_Procedure_Dependency;

   procedure Create (FA : in out Flow_Analysis_Graphs) is
   begin
      FA.TDG := FA.CFG.Create;

      --  Find all callsites for which Perform_IPFA is false and fill
      --  in the dependencies.
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : constant V_Attributes := FA.CFG.Get_Attributes (V);
         begin
            if A.Is_Callsite and not A.Perform_IPFA then
               Add_Simple_Procedure_Dependency (FA, V);
            end if;
         end;
      end loop;
   end Create;

end Flow.Interprocedural;
