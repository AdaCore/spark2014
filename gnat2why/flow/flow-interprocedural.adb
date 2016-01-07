------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . I N T E R P R O C E D U R A L                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2016, Altran UK Limited              --
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

with Flow_Classwide; use Flow_Classwide;
with Flow_Utility;   use Flow_Utility;
with Sem_Util;       use Sem_Util;
with Sinfo;          use Sinfo;
with SPARK_Util;     use SPARK_Util;
with Why;

package body Flow.Interprocedural is

   use type Flow_Graphs.Vertex_Id;

   procedure Add_Simple_Procedure_Dependency
     (FA : in out Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id);
   --  Add dependencies for a simple procedure call where we cannot
   --  perform IPFA.

   function Find_Parameter_Vertex (FA        : Flow_Analysis_Graphs;
                                   Callsite  : Flow_Graphs.Vertex_Id;
                                   Parameter : Flow_Id)
                                   return Flow_Graphs.Vertex_Id;
   --  Search for the relevant parameter vertex for a given call.

   function Find_Parameter_Vertex (FA        : Flow_Analysis_Graphs;
                                   Callsite  : Flow_Graphs.Vertex_Id;
                                   Parameter : Flow_Id)
                                   return Flow_Graphs.Vertex_Id is
   begin
      for V of FA.CDG.Get_Collection (Callsite,
                                      Flow_Graphs.Out_Neighbours)
      loop
         declare
            F : constant Flow_Id      := FA.CDG.Get_Key (V);
            A : constant V_Attributes := FA.Atr (V);
         begin
            if A.Is_Parameter then
               --  Parameters *must* be using direct mapping for both
               --  the actual and formal.
               pragma Assert (A.Parameter_Formal.Kind = Direct_Mapping);
               pragma Assert (F.Kind = Direct_Mapping);
               if Parameter.Kind = Direct_Mapping and then
                 Parameter.Variant = F.Variant and then
                 Get_Direct_Mapping_Id (Parameter) =
                 Get_Direct_Mapping_Id (A.Parameter_Formal)
               then
                  return V;
               end if;

            elsif A.Is_Global_Parameter
              or else A.Is_Implicit_Parameter
            then
               --  Globals and Implicit_Parameters can be direct mappings,
               --  record fields or magic strings, but in any case the
               --  parameter and the formal will always match in kind.
               case A.Parameter_Formal.Kind is
                  when Direct_Mapping =>
                     if Parameter.Kind = Direct_Mapping
                       and then A.Parameter_Formal.Variant = Parameter.Variant
                       and then Get_Direct_Mapping_Id (Parameter) =
                                  Get_Direct_Mapping_Id (A.Parameter_Formal)
                     then
                        return V;
                     end if;
                  when Record_Field =>
                     if Parameter.Kind = Record_Field
                       and then A.Parameter_Formal.Variant = Parameter.Variant
                       and then Get_Direct_Mapping_Id (Parameter) =
                                  Get_Direct_Mapping_Id (A.Parameter_Formal)
                     then
                        return V;
                     end if;
                  when Magic_String =>
                     if Parameter.Kind = Magic_String and then
                       A.Parameter_Formal.Variant = Parameter.Variant and then
                       Parameter.Name = A.Parameter_Formal.Name
                     then
                        return V;
                     end if;
                  when Synthetic_Null_Export =>
                     if Parameter.Kind = Synthetic_Null_Export and then
                       A.Parameter_Formal.Variant = Parameter.Variant
                     then
                        return V;
                     end if;
                  when others =>
                     raise Program_Error;
               end case;

            else
               --  We have a parameter which is neither a parameter, nor a
               --  global, nor an implicit global i.e. we have messed up in the
               --  graph construction.
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
      pragma Assert (Nkind (N) in N_Procedure_Call_Statement |
                                  N_Entry_Call_Statement);

      A : constant V_Attributes := FA.Atr (V);
      pragma Assert (A.Is_Callsite);
      pragma Assert (not A.Perform_IPFA);

      Called_Thing : constant Entity_Id := Get_Called_Entity (N);

      procedure Add_TD_Edge (A, B : Flow_Id);
      --  Add a parameter dependency edge from the input A to the
      --  output B.

      -----------------
      -- Add_TD_Edge --
      -----------------

      procedure Add_TD_Edge (A, B : Flow_Id) is
         V_A, V_B : Flow_Graphs.Vertex_Id;
      begin
         V_A := Find_Parameter_Vertex
           (FA,
            V,
            Change_Variant (A, In_View));

         V_B := Find_Parameter_Vertex
           (FA,
            V,
            Change_Variant (B, Out_View));

         FA.TDG.Add_Edge (V_A, V_B, EC_TDG);
      end Add_TD_Edge;

   --  Start of processing for Add_Simple_Procedure_Dependency

   begin
      if Has_Depends (Called_Thing)
        and then (not FA.Generating_Globals
                    or else not Rely_On_Generated_Global (Called_Thing,
                                                          FA.B_Scope))
      then
         --  We have a dependency aspect, so we should use it if:
         --     a) we have already synthesized its refined version
         --     b) we don't need to rely on its refined version

         --  The implicit in parameter for out parameters of unconstrained
         --  arrays and discriminated types is dealt with transparently
         --  here. Such an input can easily be found in the graph as a
         --  Discr_Or_Bounds parameter.
         declare
            Deps : Dependency_Maps.Map;
         begin
            Get_Depends (Subprogram           => Called_Thing,
                         Scope                => FA.B_Scope,
                         Classwide            => Is_Dispatching_Call (N),
                         Depends              => Deps,
                         Use_Computed_Globals => not FA.Generating_Globals);
            for C in Deps.Iterate loop
               declare
                  Output : constant Flow_Id := Dependency_Maps.Key (C);
                  Inputs : constant Flow_Id_Sets.Set :=
                    Dependency_Maps.Element (C);
               begin
                  for Input of Inputs loop
                     --  Output could be a null node, in which case we
                     --  do not add any edges.
                     if Present (Output) then
                        Add_TD_Edge (Input, Output);
                     else
                        Add_TD_Edge (Input, Null_Export_Flow_Id);
                     end if;
                  end loop;
               end;
            end loop;
         end;

      else
         --  We do not have a dependency aspect, so we will make up
         --  one (all outputs depend on all inputs).
         declare
            Proof_Ins : Flow_Id_Sets.Set;
            Inputs    : Flow_Id_Sets.Set;
            Outputs   : Flow_Id_Sets.Set;
            The_In    : Flow_Id;
            The_Out   : Flow_Id;
         begin
            --  Collect all the globals first.
            Get_Globals (Subprogram             => Called_Thing,
                         Scope                  => FA.B_Scope,
                         Classwide              => Is_Dispatching_Call (N),
                         Proof_Ins              => Proof_Ins,
                         Reads                  => Inputs,
                         Writes                 => Outputs,
                         Consider_Discriminants => True,
                         Use_Computed_Globals   => not FA.Generating_Globals);

            --  Add parameters.
            for E of Get_Formals (Called_Thing, N, False) loop
               if Nkind (E) in N_Entity then
                  case Ekind (E) is
                     when E_In_Parameter =>
                        The_In := Direct_Mapping_Id (Unique_Entity (E),
                                                     In_View);
                        Inputs.Insert (The_In);

                     when E_In_Out_Parameter =>
                        The_In  := Direct_Mapping_Id (Unique_Entity (E),
                                                      In_View);
                        The_Out := Direct_Mapping_Id (Unique_Entity (E),
                                                      Out_View);
                        Inputs.Insert (The_In);
                        Outputs.Insert (The_Out);

                     when E_Out_Parameter =>
                        The_In  := Direct_Mapping_Id (Unique_Entity (E),
                                                      In_View);
                        The_Out := Direct_Mapping_Id (Unique_Entity (E),
                                                      Out_View);
                        if Contains_Discriminants (The_In, FA.B_Scope)
                          or else Has_Bounds (The_In, FA.B_Scope)
                        then
                           --  Discriminated out parameters or out parameters
                           --  for which we need to keep track of the bounds
                           --  also appear as an input.
                           Inputs.Insert (The_In);
                        end if;
                        Outputs.Insert (The_Out);

                     when E_Variable | Concurrent_Kind =>
                        The_In  := Change_Variant (Concurrent_Object_Id (E),
                                                   In_View);
                        The_Out := Change_Variant (Concurrent_Object_Id (E),
                                                   Out_View);
                        Inputs.Insert (The_In);
                        if Ekind (Called_Thing) not in E_Function         |
                                                       E_Generic_Function
                        then
                           Outputs.Insert (The_Out);
                        end if;

                     when others =>
                        raise Why.Unexpected_Node;
                  end case;
               else
                  The_In  := Change_Variant (Concurrent_Object_Id (E),
                                             In_View);
                  The_Out := Change_Variant (Concurrent_Object_Id (E),
                                             Out_View);
                  Inputs.Insert (The_In);
                  if Ekind (Called_Thing) not in E_Function         |
                                                 E_Generic_Function
                  then
                     Outputs.Insert (The_Out);
                  end if;
               end if;
            end loop;

            if not Outputs.Is_Empty then
               --  Each output depends on all inputs.
               for Input of Inputs loop
                  for Output of Outputs loop
                     FA.TDG.Add_Edge (Find_Parameter_Vertex (FA, V, Input),
                                      Find_Parameter_Vertex (FA, V, Output),
                                      EC_TDG);
                  end loop;
               end loop;
            else
               --  All inputs flow into the null export vertex.
               for Input of Inputs loop
                  Add_TD_Edge (Input, Null_Export_Flow_Id);
               end loop;
            end if;
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
            A : constant V_Attributes := FA.Atr (V);
         begin
            if A.Is_Callsite and not A.Perform_IPFA then
               Add_Simple_Procedure_Dependency (FA, V);
            end if;
         end;
      end loop;
   end Create;

end Flow.Interprocedural;
