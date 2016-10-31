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

package body Flow.Interprocedural is

   procedure Add_Simple_Procedure_Dependency
     (FA : in out Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id);
   --  Add dependencies for a simple procedure call where we cannot perform
   --  IPFA.

   function Find_Parameter_Vertex (FA        : Flow_Analysis_Graphs;
                                   Callsite  : Flow_Graphs.Vertex_Id;
                                   Parameter : Flow_Id)
                                   return Flow_Graphs.Vertex_Id;
   --  Search for the relevant parameter vertex for a given call

   ---------------------------
   -- Find_Parameter_Vertex --
   ---------------------------

   function Find_Parameter_Vertex
     (FA        : Flow_Analysis_Graphs;
      Callsite  : Flow_Graphs.Vertex_Id;
      Parameter : Flow_Id)
      return Flow_Graphs.Vertex_Id is
   begin
      --   ??? why do we scan all out-neigbhour, can't we just find it in O(1)?
      for V of FA.CDG.Get_Collection (Callsite,
                                      Flow_Graphs.Out_Neighbours)
      loop
         declare
            F : Flow_Id      renames FA.CDG.Get_Key (V);
            A : V_Attributes renames FA.Atr (V);
         begin
            if A.Is_Parameter then
               --  Parameters *must* be using direct mapping for both the
               --  actual and formal.
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

   -------------------------------------
   -- Add_Simple_Procedure_Dependency --
   -------------------------------------

   procedure Add_Simple_Procedure_Dependency
     (FA : in out Flow_Analysis_Graphs;
      V  : Flow_Graphs.Vertex_Id)
   is
      N : constant Node_Id := Get_Direct_Mapping_Id (FA.CFG.Get_Key (V));
      pragma Assert (Nkind (N) in N_Procedure_Call_Statement |
                                  N_Entry_Call_Statement);

      Atr : V_Attributes renames FA.Atr (V);
      pragma Assert (Atr.Is_Callsite);
      pragma Assert (not Atr.Perform_IPFA);

      Called_Thing : constant Entity_Id := Get_Called_Entity (N);

      procedure Add_TD_Edge (A, B : Flow_Id);
      --  Add a parameter dependency edge from the input A to the output B

      -----------------
      -- Add_TD_Edge --
      -----------------

      procedure Add_TD_Edge (A, B : Flow_Id) is
         V_A : constant Flow_Graphs.Vertex_Id :=
           Find_Parameter_Vertex
             (FA,
              V,
              Change_Variant (A, In_View));

         V_B : constant Flow_Graphs.Vertex_Id :=
           Find_Parameter_Vertex
             (FA,
              V,
              Change_Variant (B, Out_View));
      begin
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
                         Use_Computed_Globals => not FA.Generating_Globals,
                         Callsite             => N);
            for C in Deps.Iterate loop
               declare
                  Output : Flow_Id          renames Dependency_Maps.Key (C);
                  Inputs : Flow_Id_Sets.Set renames Deps (C);
               begin
                  for Input of Inputs loop
                     --  Output could be a null node, in which case we do not
                     --  add any edges.
                     Add_TD_Edge (Input,
                                  (if Present (Output)
                                   then Output
                                   else Null_Export_Flow_Id));
                  end loop;
               end;
            end loop;
         end;

      else
         --  We do not have a dependency aspect, so we will make up one: all
         --  outputs depend on all inputs (but respecting the non-interference
         --  of ghost entities).
         declare
            Ignored : Flow_Id_Sets.Set;
            Inputs  : Flow_Id_Sets.Set;
            Outputs : Flow_Id_Sets.Set;
            --  Globals deduced from the contract (if available) or body

            The_In  : Flow_Id;
            The_Out : Flow_Id;

            Ghost_Subprogram : constant Boolean :=
              Is_Ghost_Entity (Called_Thing);

         begin
            --  Collect all the globals first
            Get_Globals (Subprogram             => Called_Thing,
                         Scope                  => FA.B_Scope,
                         Classwide              => Is_Dispatching_Call (N),
                         Proof_Ins              => Ignored,
                         Reads                  => Inputs,
                         Writes                 => Outputs,
                         Consider_Discriminants => True,
                         Use_Deduced_Globals    => not FA.Generating_Globals);

            --  Add parameters
            for E of Get_Explicit_Formals (Called_Thing) loop
               The_In  := Direct_Mapping_Id (Unique_Entity (E), In_View);
               The_Out := Direct_Mapping_Id (Unique_Entity (E), Out_View);

               case Ekind (E) is
                  when E_In_Parameter =>
                     Inputs.Insert (The_In);

                  when E_In_Out_Parameter =>
                     Inputs.Insert (The_In);
                     Outputs.Insert (The_Out);

                  when E_Out_Parameter =>
                     if Contains_Discriminants (The_In, FA.B_Scope)
                       or else Has_Bounds (The_In, FA.B_Scope)
                     then
                        --  Discriminated out parameters or out parameters
                        --  for which we need to keep track of the bounds
                        --  also appear as an input.
                        Inputs.Insert (The_In);
                     end if;
                     Outputs.Insert (The_Out);

                  when others =>
                     raise Program_Error;

               end case;
            end loop;

            if Ekind (Scope (Called_Thing)) = E_Protected_Type
              and then Is_External_Call (N)
            then
               declare
                  Implicit : constant Entity_Id :=
                    Get_Enclosing_Object (Prefix (Name (N)));

                  pragma Assert (Ekind (Implicit) = E_Variable);

               begin
                  The_In  := Direct_Mapping_Id (Implicit, In_View);
                  The_Out := Direct_Mapping_Id (Implicit, Out_View);

                  Inputs.Insert (The_In);
                  if Ekind (Called_Thing) /= E_Function then
                     Outputs.Insert (The_Out);
                  end if;
               end;
            end if;

            if not Outputs.Is_Empty then
               --  Each output depends on all inputs
               for Output of Outputs loop
                  declare
                     Output_V : constant Flow_Graphs.Vertex_Id :=
                       Find_Parameter_Vertex (FA, V, Output);

                     Output_Is_Proof : constant Boolean :=
                       FA.Atr (Output_V).Is_Proof;

                  begin
                     for Input of Inputs loop
                        declare
                           Input_V : constant Flow_Graphs.Vertex_Id :=
                             Find_Parameter_Vertex (FA, V, Input);

                           Input_Is_Proof : constant Boolean :=
                             FA.Atr (Input_V).Is_Proof;

                           Dependency_Allowed : constant Boolean :=
                             Output_Is_Proof
                             or else (not Ghost_Subprogram
                                      and then not Input_Is_Proof);
                           --  Ghost outputs can always be modified; non-ghost
                           --  outputs can only be modified by non-ghost
                           --  subprograms using non-ghost inputs.

                        begin
                           if Dependency_Allowed then
                              FA.TDG.Add_Edge (Input_V, Output_V, EC_TDG);
                           end if;
                        end;
                     end loop;
                  end;
               end loop;
            else
               --  All inputs flow into the null export vertex
               for Input of Inputs loop
                  Add_TD_Edge (Input, Null_Export_Flow_Id);
               end loop;
            end if;
         end;
      end if;
   end Add_Simple_Procedure_Dependency;

   ------------
   -- Create --
   ------------

   procedure Create (FA : in out Flow_Analysis_Graphs) is
   begin
      FA.TDG := FA.CFG.Create;

      --  Find all callsites for which Perform_IPFA is false and fill
      --  in the dependencies.
      for V of FA.CFG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : V_Attributes renames FA.Atr (V);
         begin
            if A.Is_Callsite and not A.Perform_IPFA then
               Add_Simple_Procedure_Dependency (FA, V);
            end if;
         end;
      end loop;
   end Create;

end Flow.Interprocedural;
