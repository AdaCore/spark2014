------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--        F L O W . C O N T R O L _ D E P E N D E N C E _ G R A P H         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2026, Capgemini Engineering              --
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

package body Flow.Control_Dependence_Graph is

   procedure Create (FA : in out Flow_Analysis_Graphs) is

      procedure Sanity_Check (V, CV : Flow_Graphs.Vertex_Id)
      with Ghost;
      --  Apply sanity checking to V and CV, which are a call parameter vertex
      --  and its corresponding call vertex, respectively.

      ------------------
      -- Sanity_Check --
      ------------------

      pragma Annotate (Xcov, Exempt_On, "Ghost code");
      procedure Sanity_Check (V, CV : Flow_Graphs.Vertex_Id) is
         use type Flow_Graphs.Vertex_Id;
      begin
         --  Sanity check that we will not lose control dependence
         for P of FA.CDG.Get_Collection (V, Flow_Graphs.In_Neighbours) loop
            if P = V then
               --  Self dependence does not appear for parameters, so it won't
               --  disappear either.
               raise Program_Error;

            elsif FA.CDG.Non_Trivial_Path_Exists (P, CV) then
               --  The call vertex is ultimately control dependent on the
               --  in-neighbour we are eliminating from our parameter vertex,
               --  so we don't really lose anything.
               null;

            --  Writes to parameters of mode OUT depend on the exception being
            --  raised.

            elsif FA.Atr (P).Is_Call_Exception then
               pragma Assert (FA.Atr (V).Is_Parameter);
               pragma Assert (FA.CFG.Get_Key (V).Variant = Out_View);
               pragma Assert (FA.Atr (V).Call_Vertex = CV);

            else
               --  Bath, we have a problem
               raise Program_Error;
            end if;
         end loop;

         --  Sanity check that we won't lose outwards control influence,
         --  i.e. check that parameter itself doesn't influence control flow.

         if FA.CDG.Out_Neighbour_Count (V) > 0 then
            raise Program_Error;
         end if;
      end Sanity_Check;
      pragma Annotate (Xcov, Exempt_Off);

      --  Local variables

      Reversed_CFG : Flow_Graphs.Graph;

      --  Start of processing for Create

   begin
      --  Reverse CFG and add an edge from end -> start
      Reversed_CFG := FA.CFG.Invert;
      Reversed_CFG.Add_Edge (FA.End_Vertex, FA.Start_Vertex, EC_Default);

      --  The CDG is simply the post-dominance frontier.
      FA.CDG := Reversed_CFG.Dominance_Frontier (FA.End_Vertex);

      --  Fix call nodes. As they appear as a linear sequence in the CFG the
      --  call vertex and each parameter vertex will all be control dependent
      --  on the same node. For clarity, we want all parameter vertices to be
      --  control dependent on the call vertex.
      --
      --  There are a few complications here, triggered by loops which are
      --  executed at least once (i.e. general loops and for loops over a
      --  statically non-empty range). We have quite involved sanity checks
      --  which push up the complexity (path finding is linear), but this
      --  kind of graph fiddling is much easier to justify that way.

      for V of FA.CDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            A : V_Attributes renames FA.Atr (V);
         begin
            if A.Is_Parameter
              or else A.Is_Global_Parameter
              or else A.Is_Implicit_Parameter
            then
               declare
                  CV : constant Flow_Graphs.Vertex_Id := A.Call_Vertex;

               begin
                  Sanity_Check (V => V, CV => CV);

                  FA.CDG.Clear_Vertex (V);
                  FA.CDG.Add_Edge (CV, V, EC_Default);
               end;

            --  For subprogram calls that might raise some exception, we add
            --  dependency edges to the in-parameters (because the exact
            --  exception being raised depends on the input parameters) and to
            --  the call vertex (because when there are no input parameters
            --  then the exact exception depends on the call itself).

            --  We do this both for the vertex, where the control flow branches
            --  into exceptional execution, and for the havoc vertex, where the
            --  control flow branches into a particular exception. Note: we
            --  could have single vertex where either normal or any of the
            --  exceptional executions is selected, but there we would need a
            --  havoc vertex on every exceptional execution paths.

            elsif A.Is_Call_Exception or else A.Is_Param_Havoc then
               declare
                  Prev    : Flow_Graphs.Vertex_Id := V;
                  In_Deps : Vertex_Sets.Set;
               begin
                  --  Collect incoming edges and remove them

                  for In_Dep of
                    FA.CDG.Get_Collection (V, Flow_Graphs.In_Neighbours)
                  loop
                     In_Deps.Insert (In_Dep);
                  end loop;

                  for In_Dep of In_Deps loop
                     FA.CDG.Remove_Edge (In_Dep, V);
                  end loop;

                  loop
                     Prev := FA.CFG.Parent (Prev);

                     declare
                        Prev_Atr : V_Attributes renames FA.Atr (Prev);
                     begin
                        if Prev_Atr.Is_Callsite then
                           FA.CDG.Add_Edge (Prev, V, EC_Default);
                           exit;

                        elsif Prev_Atr.Is_Parameter then
                           if FA.CFG.Get_Key (Prev).Variant = In_View then
                              FA.CDG.Add_Edge (Prev, V, EC_Default);
                           end if;

                        elsif Prev_Atr.Is_Global_Parameter
                          or else Prev_Atr.Is_Implicit_Parameter
                        then
                           pragma
                             Assert
                               (Prev_Atr.Parameter_Formal.Variant
                                in In_View | Out_View);
                           if Prev_Atr.Parameter_Formal.Variant = In_View then
                              if Prev_Atr.Is_Assertion then
                                 pragma Assert (Prev_Atr.Is_Global_Parameter);
                              else
                                 FA.CDG.Add_Edge (Prev, V, EC_Default);
                              end if;
                           end if;
                        elsif Prev_Atr.Is_Call_Exception then
                           null;
                        else
                           raise Program_Error;
                        end if;
                     end;
                  end loop;
               end;
            end if;
         end;
      end loop;
   end Create;

end Flow.Control_Dependence_Graph;
