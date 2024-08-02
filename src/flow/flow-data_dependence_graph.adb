------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--           F L O W . D A T A _ D E P E N D E N C E _ G R A P H            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2013-2024, Capgemini Engineering              --
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

with Sem_Util;               use Sem_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with Flow_Utility;           use Flow_Utility;

package body Flow.Data_Dependence_Graph is

   ------------
   -- Create --
   ------------

   procedure Create (FA : in out Flow_Analysis_Graphs) is

      function Edge_Selector (A, B : Flow_Graphs.Vertex_Id)
                              return Boolean;
      --  Check if we should go down the given edge based on colour

      function Potential_Definite_Calls
        (Calls : Node_Sets.Set)
         return Flow_Id_Sets.Set;
      --  Returns subprograms whose calls need to be checked for being
      --  definitive (as opposed to being conditional or being only called
      --  in assertions).

      procedure Process
        (V_D : Flow_Graphs.Vertex_Id;
         TV  : out Flow_Graphs.Simple_Traversal_Instruction);
      --  Process the vertex V_D to create the corresponding vertex in the DDG

      -------------------
      -- Edge_Selector --
      -------------------

      function Edge_Selector (A, B : Flow_Graphs.Vertex_Id)
                              return Boolean is
        (case FA.CFG.Edge_Colour (A, B) is
            when EC_Default | EC_Inf => True,
            when EC_Barrier          => False,
            when others              => raise Program_Error);

      ------------------------------
      -- Potential_Definite_Calls --
      ------------------------------

      function Potential_Definite_Calls
        (Calls : Node_Sets.Set)
         return Flow_Id_Sets.Set
      is
         Check : Flow_Id_Sets.Set;
      begin
         if FA.Generating_Globals
           and then FA.Is_Generative
         then
            for E of Calls loop
               if (Ekind (E) in E_Procedure | E_Entry
                    or else Is_Function_With_Side_Effects (E))
                 and then (not Has_User_Supplied_Globals (E)
                           or else Rely_On_Generated_Global (E, FA.B_Scope))
               then
                  Check.Insert (Direct_Mapping_Id (E));
               end if;
            end loop;
         end if;
         return Check;
      end Potential_Definite_Calls;

      -------------
      -- Process --
      -------------

      procedure Process
        (V_D : Flow_Graphs.Vertex_Id;
         TV  : out Flow_Graphs.Simple_Traversal_Instruction)
      is
         Atr_Def : V_Attributes renames FA.Atr (V_D);

         use type Flow_Id_Sets.Set;

         Combined_Defined : constant Flow_Id_Sets.Set :=
           Atr_Def.Variables_Defined or Atr_Def.Volatiles_Read or
           Potential_Definite_Calls
             (To_Subprograms (Atr_Def.Subprogram_Calls));

         use type Flow_Graphs.Vertex_Id;

      begin
         TV := Flow_Graphs.Continue;

         --  If this vertex defines a component of a record assignment, then
         --  connect it with a corresponding vertex with variables used for the
         --  new value of this record component. This is similar to connecting
         --  'In and 'Out vertices of procedure calls according to the Depends
         --  contract, which happens when building TDG.

         if Atr_Def.Record_RHS /= Flow_Graphs.Null_Vertex then
            FA.DDG.Add_Edge (Atr_Def.Record_RHS, V_D, EC_DDG);
         end if;

         for Var of Combined_Defined loop
            declare
               procedure Visitor
                 (V_U  : Flow_Graphs.Vertex_Id;
                  TV_U : out Flow_Graphs.Simple_Traversal_Instruction);
               --  For Var, check if there is a def-use link from V_D to V_U.
               --  Stop traversal if node V_U also defined Var.

               -------------
               -- Visitor --
               -------------

               procedure Visitor
                 (V_U  : Flow_Graphs.Vertex_Id;
                  TV_U : out Flow_Graphs.Simple_Traversal_Instruction)
               is
                  Atr : V_Attributes renames FA.Atr (V_U);
               begin
                  if Atr.Variables_Used.Contains (Var) then
                     FA.DDG.Add_Edge (V_D, V_U, EC_DDG);
                  end if;

                  if Atr.Variables_Defined.Contains (Var)
                    or else Atr.Volatiles_Read.Contains (Var)
                  then
                     if (Atr_Def.Is_Parameter
                         or else Atr_Def.Is_Global_Parameter
                         or else Atr_Def.Is_Implicit_Parameter)
                       and then (Atr.Is_Parameter
                                 or else Atr.Is_Global_Parameter
                                 or else Atr.Is_Implicit_Parameter)
                       and then Atr_Def.Call_Vertex = Atr.Call_Vertex
                     then
                        --  We have a definite order in which we assign out
                        --  parameters in flow, but this is just an assumption
                        --  which means we might get an incorrect graph when
                        --  aliasing is present. Here we allow multiple out
                        --  vertices from the same procedure call to flow
                        --  into the same variable.
                        TV_U := Flow_Graphs.Continue;
                     else
                        TV_U := Flow_Graphs.Skip_Children;
                     end if;

                  --  Deal with calls to potentially definite calls, which is
                  --  only needed in phase 1 and only if generating globals for
                  --  the currently analysed subprogram.
                  --
                  --  Note: the linear search below is theoretically
                  --  inefficient, but in practice we don't expect many
                  --  function calls appearing toghether with a procedure or
                  --  entry call, i.e. inside its actual parameters.

                  elsif FA.Generating_Globals
                    and then FA.Is_Generative
                    and then Var.Kind = Direct_Mapping
                    and then
                      (declare
                         E : constant Entity_Id := Get_Direct_Mapping_Id (Var);
                       begin
                         Ekind (E) in E_Procedure | E_Entry
                           or else
                         (Ekind (E) = E_Function
                           and then Is_Function_With_Side_Effects (E)))
                    and then
                      (for some SC of Atr.Subprogram_Calls =>
                         SC.E = Get_Direct_Mapping_Id (Var))
                  then
                     TV_U := Flow_Graphs.Skip_Children;

                  else
                     TV_U := Flow_Graphs.Continue;
                  end if;
               end Visitor;

            begin
               --  Check for self-dependency (i.e. X := X + 1)
               if Atr_Def.Variables_Used.Contains (Var) then
                  FA.DDG.Add_Edge (V_D, V_D, EC_DDG);
               end if;

               --  Flag all def-used chains rooted at V_D
               FA.CFG.DFS (Start         => V_D,
                           Include_Start => False,
                           Visitor       => Visitor'Access,
                           Edge_Selector => Edge_Selector'Access);

               for Vol of Atr_Def.Volatiles_Written loop
                  declare
                     V_Final : constant Flow_Graphs.Vertex_Id :=
                       FA.CFG.Get_Vertex (Change_Variant (Vol, Final_Value));

                  begin
                     if V_Final /= Flow_Graphs.Null_Vertex then
                        --  If V_Final is null, then we're doing something
                        --  involving a variable that has been missed out
                        --  of the global annotation. We just ignore the
                        --  connection in that case, and flow analysis
                        --  sanity check will pick up the pieces later.
                        FA.DDG.Add_Edge (V_D, V_Final, EC_DDG);
                     end if;
                  end;
               end loop;
            end;
         end loop;
      end Process;

      --  Local variables

      Unused : Flow_Graphs.Simple_Traversal_Instruction;

   --  Start of processing for Create

   begin
      FA.DDG := FA.CFG.Create;

      --  Process 'Initial vertices (leading to the Start_Vertex); those
      --  vertices can have 'Initial_Grouping in-neighbours themselves, but
      --  they do not affect DDG.

      for V_D of FA.CFG.Get_Collection
        (FA.Start_Vertex, Flow_Graphs.In_Neighbours)
      loop
         pragma Assert (FA.CFG.Get_Key (V_D).Variant = Initial_Value);
         Process (V_D, Unused);
      end loop;

      --  Process remaining live vertices (coming from the Start_Vertex)

      FA.CFG.DFS
        (Start         => FA.Start_Vertex,
         Include_Start => True,
         Visitor       => Process'Access,
         Edge_Selector => Edge_Selector'Access);

   end Create;

end Flow.Data_Dependence_Graph;
