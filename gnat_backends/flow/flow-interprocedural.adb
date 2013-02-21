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

with Aspects;  use Aspects;
with Nlists;   use Nlists;
with Sem_Util; use Sem_Util;
with Sinfo;    use Sinfo;

with Treepr; use Treepr;

with Why;

package body Flow.Interprocedural is

   procedure Add_Simple_Procedure_Dependency
     (FA : in out Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id);
   --  Add dependencies for a simple procedure call where we cannot
   --  perform IPFA.

   function Process_Depends (D : Node_Id) return Flow_Graphs.T;

   function Find_Parameter_Vertex (CDG       : Flow_Graphs.T;
                                   Callsite  : Flow_Graphs.Vertex_Id;
                                   Parameter : Flow_Id)
                                   return Flow_Graphs.Vertex_Id;
   --  Search for the relevant parameter vertex for a given call.

   function Process_Depends (D : Node_Id) return Flow_Graphs.T is
      G : Flow_Graphs.T;
      Row : Node_Id;
      LHS : Node_Id;
      RHS : Node_Id;
   begin
      G := Flow_Graphs.Create;
      Row := First (Component_Associations (D));
      while Row /= Empty loop
         Print_Node_Subtree (Row);
         LHS := First (Choices (Row));
         while LHS /= Empty loop
            Print_Node_Subtree (LHS);

            RHS := Expression (Row);
            Print_Node_Subtree (RHS);

            LHS := Next (LHS);
         end loop;

         Row := Next (Row);
      end loop;
      return G;
   end Process_Depends;

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
            case Parameter.Kind is
               when Direct_Mapping =>
                  if Parameter.Variant = F.Variant and then
                    Parameter.Kind = F.Kind and then
                    Get_Direct_Mapping_Id (Parameter) =
                    Get_Direct_Mapping_Id (A.Parameter_Formal) then
                     return V;
                  end if;
               when others =>
                  raise Why.Not_Implemented;
            end case;
         end;
      end loop;
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
   begin
      if Has_Aspect (Called_Procedure, Aspect_Depends) then
         --  We have a dependency aspect, so we should use it.
         declare
            Depends : constant Node_Id :=
              Find_Aspect (Called_Procedure, Aspect_Depends);
         begin
            Print_Graph ("depends", Process_Depends (Depends));
         end;

         raise Why.Not_Implemented;

      else
         --  We do not have a dependency aspect, so we will make up
         --  one (all outputs depend on all inputs).
         declare
            Inputs  : Flow_Id_Sets.Set;
            Outputs : Flow_Id_Sets.Set;
            E       : Entity_Id;
         begin
            Print_Node_Subtree (Called_Procedure);

            E := First_Entity (Called_Procedure);
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
               E := Next_Entity (E);
            end loop;

            --  TODO: Collect globals

            for I of Inputs loop
               for O of Outputs loop
                  FA.TDG.Add_Edge (Find_Parameter_Vertex (FA.CDG, V, I),
                                   Find_Parameter_Vertex (FA.CDG, V, O),
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
