------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--     A S I S _ U L . G L O B A L _ S T A T E . C G . S P A R K I F Y      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

pragma Ada_2005;

with Ada.Characters.Conversions;       use Ada.Characters.Conversions;

package body ASIS_UL.Global_State.CG.Sparkify is

   procedure Set_Global_Sets
     (El                         :     Asis.Element;
      Reads, Writes, Read_Writes : out Node_Lists.Set);

   function List_Of_Globals
     (S   : Node_Lists.Set;
      Sep : Wide_String) return Unbounded_Wide_String;

   procedure Set_Global_Sets
     (El                         :     Asis.Element;
      Reads, Writes, Read_Writes : out Node_Lists.Set)
   is
      N : constant GS_Node_Id := Corresponding_Node (El);
   begin
      Reads  := Indirect_Reads (N).all;
      Writes := Indirect_Writes (N).all;

      Add_SLOC_Node_List_To_Node_List (Reads, Direct_Reads (N).all);
      Add_SLOC_Node_List_To_Node_List (Writes, Direct_Writes (N).all);

      Read_Writes := Node_Lists.Intersection (Reads, Writes);
      Reads       := Node_Lists.Difference (Reads, Read_Writes);
      Writes      := Node_Lists.Difference (Writes, Read_Writes);
   end Set_Global_Sets;

   function List_Of_Globals
     (S   : Node_Lists.Set;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Result : Unbounded_Wide_String;
      Next   : Node_Lists.Cursor := S.First;
   begin

      --  First take into account the first global variable
      if Node_Lists.Has_Element (Next) then
         declare
            Tmp : constant String := GS_Node_Name (Node_Lists.Element (Next));
         begin
            Result := To_Unbounded_Wide_String (To_Wide_String (Tmp));
            Node_Lists.Next (Next);
         end;
      end if;

      --  Then concatenate all remaining global variables
      while Node_Lists.Has_Element (Next) loop
         declare
            Tmp : constant String := GS_Node_Name (Node_Lists.Element (Next));
         begin
            Result := Result & Sep & (To_Wide_String (Tmp));
            Node_Lists.Next (Next);
         end;
      end loop;

      return Result;

   end List_Of_Globals;

   procedure Global_Effects
     (El              : Asis.Element;
      Sep             : Wide_String;
      Reads_Str       : out Unbounded_Wide_String;
      Writes_Str      : out Unbounded_Wide_String;
      Read_Writes_Str : out Unbounded_Wide_String)
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      Reads_Str       := List_Of_Globals (Reads, Sep);
      Writes_Str      := List_Of_Globals (Writes, Sep);
      Read_Writes_Str := List_Of_Globals (Read_Writes, Sep);
   end Global_Effects;

   function Global_Reads
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      return List_Of_Globals (Reads, Sep);
   end Global_Reads;

   function All_Global_Reads
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      Node_Lists.Union (Reads, Read_Writes);
      return List_Of_Globals (Reads, Sep);
   end All_Global_Reads;

   function Global_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      return List_Of_Globals (Writes, Sep);
   end Global_Writes;

   function All_Global_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      Node_Lists.Union (Writes, Read_Writes);
      return List_Of_Globals (Writes, Sep);
   end All_Global_Writes;

   function Global_Read_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      return List_Of_Globals (Read_Writes, Sep);
   end Global_Read_Writes;

end ASIS_UL.Global_State.CG.Sparkify;
