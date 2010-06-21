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

with Asis;                             use Asis;
with Asis.Elements;                    use Asis.Elements;
with Asis.Extensions.Flat_Kinds;       use Asis.Extensions.Flat_Kinds;

package body ASIS_UL.Global_State.CG.Sparkify is

   procedure Set_Global_Sets
     (El                         :     Asis.Element;
      Reads, Writes, Read_Writes : out Node_Lists.Set);

   function List_Of_Globals
     (El  : Asis.Element;
      S   : Node_Lists.Set;
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
     (El  : Asis.Element;
      S   : Node_Lists.Set;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Result    : Unbounded_Wide_String;
      Next      : Node_Lists.Cursor := S.First;
      Encl_El   : Asis.Element;
      Encl_Name : Unbounded_Wide_String;

      --  Return the package enclosing element El, if any
      function Enclosing_Package (El : Asis.Element) return Asis.Element;

      function Enclosing_Package (El : Asis.Element) return Asis.Element is
      begin
         if Flat_Element_Kind (El) = A_Package_Declaration
           or else Flat_Element_Kind (El) = A_Package_Body_Declaration then
            return El;
         else
            declare
               Encl_El : constant Asis.Element := Enclosing_Element (El);
            begin
               if Is_Nil (Encl_El) then
                  return Encl_El;
               else
                  return Enclosing_Package (Encl_El);
               end if;
            end;
         end if;
      end Enclosing_Package;

      --  Return the name of element Next, taking into account the fact that
      --  the element may be included in the current package (whose name is
      --  Encl_Name), in which case no prefixing is necessary.
      --  This is a hackish way of detecting scoping, which is only relevant
      --  for this prototype, and because GS_Node_Id in ASIS_UL.Global_State
      --  only provide names.
      function Name_Of_Next_Element
        (Next : Node_Lists.Cursor) return Wide_String;

      function Name_Of_Next_Element
        (Next : Node_Lists.Cursor) return Wide_String
      is
         N   : constant GS_Node_Id := Node_Lists.Element (Next);
         S   : constant Scope_Id   := GS_Node_Enclosing_Scope (N);
         Tmp : constant String     := GS_Node_Name (N);
      begin
         if Present (S) and then GS_Node_Kind (S) = A_Package then
            declare
               Pack_Name : constant Wide_String :=
                             To_Wide_String (GS_Node_Name (S));
            begin
               if Pack_Name /= Encl_Name then
                  Result := Result & Pack_Name & ".";
               end if;
            end;
         end if;
         return To_Wide_String (Tmp);
      end Name_Of_Next_Element;
   begin
      Encl_El := Enclosing_Package (El);

      if not Is_Nil (Encl_El) then
         Encl_Name :=
           To_Unbounded_Wide_String
             (To_Wide_String (GS_Node_Name (Corresponding_Node (Encl_El))));
      end if;

      --  First take into account the first global variable
      if Node_Lists.Has_Element (Next) then
         Result := Result & Name_Of_Next_Element (Next);
         Node_Lists.Next (Next);
      end if;

      --  Then concatenate all remaining global variables
      while Node_Lists.Has_Element (Next) loop
         Result := Result & Sep & Name_Of_Next_Element (Next);
         Node_Lists.Next (Next);
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
      Reads_Str       := List_Of_Globals (El, Reads, Sep);
      Writes_Str      := List_Of_Globals (El, Writes, Sep);
      Read_Writes_Str := List_Of_Globals (El, Read_Writes, Sep);
   end Global_Effects;

   function Global_Reads
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      return List_Of_Globals (El, Reads, Sep);
   end Global_Reads;

   function All_Global_Reads
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      Node_Lists.Union (Reads, Read_Writes);
      return List_Of_Globals (El, Reads, Sep);
   end All_Global_Reads;

   function Global_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      return List_Of_Globals (El, Writes, Sep);
   end Global_Writes;

   function All_Global_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      Node_Lists.Union (Writes, Read_Writes);
      return List_Of_Globals (El, Writes, Sep);
   end All_Global_Writes;

   function Global_Read_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String
   is
      Reads, Writes, Read_Writes : Node_Lists.Set;
   begin
      Set_Global_Sets (El, Reads, Writes, Read_Writes);
      return List_Of_Globals (El, Read_Writes, Sep);
   end Global_Read_Writes;

end ASIS_UL.Global_State.CG.Sparkify;
