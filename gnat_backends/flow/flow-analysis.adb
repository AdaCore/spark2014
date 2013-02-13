------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                        F L O W . A N A L Y S I S                         --
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

with Errout; use Errout;
with Why;

package body Flow.Analysis is

   procedure Error_Msg_Flow (Msg : String; F : Flow_Id);
   --  Output an error message attaced to the given flow_id thing.

   procedure Error_Msg_Flow (Msg : String; L, F : Flow_Id);
   --  Output an error message attaced to the given flow_id thing L.

   procedure Error_Msg_Flow (Msg : String; F : Flow_Id)
   is
   begin
      case F.Kind is
         when Direct_Mapping =>
            Error_Msg_N (Msg, Get_Direct_Mapping_Id (F));
         when others =>
            raise Why.Not_Implemented;
      end case;
   end Error_Msg_Flow;

   procedure Error_Msg_Flow (Msg : String; L, F : Flow_Id)
   is
   begin
      if L.Kind = Direct_Mapping and F.Kind = Direct_Mapping then
         Error_Msg_NE (Msg,
                       Get_Direct_Mapping_Id (L),
                       Get_Direct_Mapping_Id (F));
      else
         raise Why.Not_Implemented;
      end if;
   end Error_Msg_Flow;

   procedure Find_Ineffective_Imports
     (FA : Flow_Analysis_Graphs)
   is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if the given vertex V is a final-use vertex.

      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value;
      end Is_Final_Use;
   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr : constant V_Attributes := FA.PDG.Get_Attributes (V);
         begin
            if Key.Variant = Initial_Value and then Atr.Is_Initialised then
               if not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use'Access) then
                  Error_Msg_Flow ("ineffective import!", Key);
               end if;
            end if;
         end;
      end loop;
   end Find_Ineffective_Imports;

   procedure Find_Ineffective_Statements
     (FA : Flow_Analysis_Graphs)
   is
      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean;
      --  Checks if the given vertex V is a final-use vertex.

      function Is_Final_Use (V : Flow_Graphs.Vertex_Id) return Boolean is
      begin
         return FA.PDG.Get_Key (V).Variant = Final_Value;
      end Is_Final_Use;
   begin
      for V of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key : constant Flow_Id      := FA.PDG.Get_Key (V);
            Atr : constant V_Attributes := FA.PDG.Get_Attributes (V);
         begin
            if Atr.Is_Program_Node then
               if not FA.PDG.Non_Trivial_Path_Exists
                 (V, Is_Final_Use'Access) then
                  Error_Msg_Flow ("ineffective statement!", Key);
               end if;
            end if;
         end;
      end loop;
   end Find_Ineffective_Statements;

   procedure Find_Use_Of_Uninitialised_Variables
     (FA : Flow_Analysis_Graphs)
   is
   begin
      for V_Initial of FA.PDG.Get_Collection (Flow_Graphs.All_Vertices) loop
         declare
            Key_I : constant Flow_Id      := FA.PDG.Get_Key (V_Initial);
            Atr_I : constant V_Attributes := FA.PDG.Get_Attributes (V_Initial);
         begin
            if Key_I.Variant = Initial_Value and then
              not Atr_I.Is_Initialised then
               for V_Use of FA.PDG.Get_Collection
                 (V_Initial, Flow_Graphs.Out_Neighbours) loop
                  declare
                     Key_U : constant Flow_Id := FA.PDG.Get_Key (V_Use);
                  begin
                     if Key_U.Variant = Final_Value then
                        Error_Msg_Flow ("may never be initialized!",
                                        Key_U);
                     else
                        Error_Msg_Flow ("use of uninitialized variable &!",
                                        Key_U, Key_I);
                     end if;
                  end;
               end loop;
            end if;
         end;
      end loop;
   end Find_Use_Of_Uninitialised_Variables;

end Flow.Analysis;
