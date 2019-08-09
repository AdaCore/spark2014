------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                 F L O W . I N T E R P R O C E D U R A L                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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
with Sem_Aux;        use Sem_Aux;
with Sinfo;          use Sinfo;

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
               --  Global and implicit parameters can be direct mappings,
               --  magic strings or synthetic null exports, but in any case
               --  the parameter and the formal will always match in kind.
               case A.Parameter_Formal.Kind is
                  when Direct_Mapping =>
                     if Parameter.Kind = Direct_Mapping
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

      procedure Add_TD_Edge (A, B : Flow_Id)
      with Pre => A.Variant = Normal_Use and then B.Variant = Normal_Use;
      --  Add a parameter dependency edge from the input A to the output B.
      --  This is only meant to be called with Normal_Use parameters, exactly
      --  as they come from Get_Depends.

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
         --  arrays and discriminated types is dealt with transparently here.
         --  Such an input can easily be found in the graph as a
         --  Discr_Or_Bounds parameter.
         declare
            Deps : Dependency_Maps.Map;

         begin
            Get_Depends (Subprogram           => Called_Thing,
                         Scope                => FA.B_Scope,
                         Classwide            =>
                           Flow_Classwide.Is_Dispatching_Call (N),
                         Depends              => Deps,
                         Use_Computed_Globals => not FA.Generating_Globals);

            for C in Deps.Iterate loop
               declare
                  Output : Flow_Id          renames Dependency_Maps.Key (C);
                  Inputs : Flow_Id_Sets.Set renames Deps (C);

               begin
                  Remove_Constants (Inputs);

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
            Globals : Global_Flow_Ids;
            --  Globals deduced from the contract (if available) or body

            The_In  : Flow_Id;
            The_Out : Flow_Id;

            Ghost_Subprogram : constant Boolean :=
              Is_Ghost_Entity (Called_Thing);

            function Is_Implicit_Input (F : Flow_Id) return Boolean;
            --  Returns True iff F should augument the explicit input set of
            --  a subprogram, as described in SPARK RM 6.1.5(5): "[is of] an
            --  unconstrained array subtype, an unconstrained discriminated
            --  subtype, a tagged type (with one exception), or a type having
            --  a subcomponent of an unconstrained discriminated subtype".
            --
            --  ??? the tagged type part of the above rule is not yet detected

            -----------------------
            -- Is_Implicit_Input --
            -----------------------

            function Is_Implicit_Input (F : Flow_Id) return Boolean is
              (Has_Bounds (F, FA.B_Scope)
                 or else
               (Contains_Discriminants (F, FA.B_Scope)
                  and then
                not Is_Constrained (Get_Type (F, FA.B_Scope))));

         begin
            --  Collect all the globals first
            Get_Globals (Subprogram          => Called_Thing,
                         Scope               => FA.B_Scope,
                         Classwide           =>
                           Flow_Classwide.Is_Dispatching_Call (N),
                         Globals             => Globals,
                         Use_Deduced_Globals => not FA.Generating_Globals);

            Remove_Constants (Globals.Inputs);

            --  Add parameters
            for E of Get_Explicit_Formals (Called_Thing) loop
               The_In  := Direct_Mapping_Id (E, In_View);
               The_Out := Direct_Mapping_Id (E, Out_View);

               case Ekind (E) is
                  when E_In_Parameter =>
                     Globals.Inputs.Insert (The_In);

                  when E_In_Out_Parameter =>
                     Globals.Inputs.Insert (The_In);
                     Globals.Outputs.Insert (The_Out);

                  when E_Out_Parameter =>
                     if Is_Implicit_Input (The_In) then
                        Globals.Inputs.Insert (The_In);
                     end if;
                     Globals.Outputs.Insert (The_Out);

                  when others =>
                     raise Program_Error;

               end case;
            end loop;

            if Ekind (Scope (Called_Thing)) = E_Protected_Type then
               declare
                  Implicit : constant Flow_Id :=
                    Direct_Mapping_Id (Scope (Called_Thing));

               begin
                  The_In  := Change_Variant (Implicit, In_View);
                  The_Out := Change_Variant (Implicit, Out_View);

                  --  The protected object may already appear as a (generated)
                  --  Global, e.g. when a protected subprogram calls an
                  --  (external) proxy that externally calls a protected
                  --  subprogram of the same object. External calls will be
                  --  rejected by the flow analysis later, but now we must
                  --  conservatively Include and not Insert the protected
                  --  object. If the current implicit parameter is the
                  --  protected type we still include it.
                  Globals.Inputs.Include (The_In);
                  if Ekind (Called_Thing) /= E_Function then
                     Globals.Outputs.Include (The_Out);
                  end if;
               end;
            end if;

            if Globals.Outputs.Is_Empty then
               if not Globals.Inputs.Is_Empty then
                  --  Every input flows into the null export vertex
                  declare
                     Output_V : constant Flow_Graphs.Vertex_Id :=
                       Find_Parameter_Vertex
                         (FA, V,
                          Change_Variant (Null_Export_Flow_Id, Out_View));

                  begin
                     for Input of Globals.Inputs loop
                        FA.TDG.Add_Edge
                          (Find_Parameter_Vertex (FA, V, Input),
                           Output_V,
                           EC_TDG);
                     end loop;
                  end;
               end if;
            else
               --  Every input flows into all outputs
               for Output of Globals.Outputs loop
                  declare
                     Output_V : constant Flow_Graphs.Vertex_Id :=
                       Find_Parameter_Vertex (FA, V, Output);

                     Output_Is_Ghost : constant Boolean :=
                       Is_Ghost_Entity (Output);

                     The_In : constant Flow_Id :=
                       Change_Variant (Output, In_View);

                  begin
                     if not Globals.Inputs.Contains (The_In)
                       and then Is_Implicit_Input (The_In)
                     then
                        Globals.Inputs.Insert (The_In);
                     end if;

                     for Input of Globals.Inputs loop
                        declare
                           Dependency_Allowed : constant Boolean :=
                             Output_Is_Ghost
                               or else
                             Is_Abstract_State (Output)
                               or else
                             (not Ghost_Subprogram
                              and then not Is_Ghost_Entity (Input));
                           --  Ghost outputs can always be modified; non-ghost
                           --  abstract states too, because they might contain
                           --  ghost constituents; non-ghost outputs can only
                           --  be modified by non-ghost subprograms using
                           --  non-ghost inputs.

                        begin
                           if Dependency_Allowed then
                              FA.TDG.Add_Edge
                                (Find_Parameter_Vertex (FA, V, Input),
                                 Output_V,
                                 EC_TDG);
                           end if;
                        end;
                     end loop;
                  end;
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

      --  Find all callsites for which Perform_IPFA is false and fill in the
      --  dependencies.
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
