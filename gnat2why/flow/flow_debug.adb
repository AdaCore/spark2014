------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W _ D E B U G                            --
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

with Ada.Characters.Latin_1; use Ada.Characters.Latin_1;
with Ada.Containers;
with Ada.Real_Time;          use Ada.Real_Time;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Atree;                  use Atree;
with Output;                 use Output;
with Sprint;                 use Sprint;

use type Ada.Containers.Count_Type;

package body Flow_Debug is

   The_Time       : Time;
   The_Start_Time : Time;

   Temp_String : Unbounded_String;

   procedure Add_To_Temp_String (S : String);
   --  Helper subprogram to add to the buffer.

   ------------------------
   -- Add_To_Temp_String --
   ------------------------

   procedure Add_To_Temp_String (S : String) is
      Prev : Character := ' ';
   begin
      for C of S loop
         if Prev = ' ' and then C = ' ' then
            null;
         else
            case C is
               when Ada.Characters.Latin_1.CR =>
                  null;
               when Ada.Characters.Latin_1.LF =>
                  if Prev not in '(' | ')' then
                     Append (Temp_String, ' ');
                  end if;
                  Prev := C;
               when others =>
                  Append (Temp_String, C);
                  Prev := C;
            end case;
         end if;
      end loop;
   end Add_To_Temp_String;

   ---------------
   -- Init_Time --
   ---------------

   procedure Init_Time (S : String) is
   begin
      The_Time := Clock;
      The_Start_Time := The_Time;
      Write_Str (S);
      Write_Eol;
   end Init_Time;

   ---------------
   -- Note_Time --
   ---------------

   procedure Note_Time (S : String) is
      Now : constant Time := Clock;
   begin
      Write_Str (S & " (" & To_Duration (Now - The_Time)'Img & ")");
      Write_Eol;
      The_Time := Now;
   end Note_Time;

   ----------------
   -- Final_Time --
   ----------------

   procedure Final_Time (S : String) is
      Now : constant Time := Clock;
   begin
      Write_Str (S & " (total: " &
                 To_Duration (Now - The_Start_Time)'Img & ")");
      Write_Eol;
   end Final_Time;

   --------------------
   -- Print_Node_Set --
   --------------------

   procedure Print_Node_Set (S : Node_Sets.Set) is
   begin
      if S.Length > 0 then
         Write_Str ("Node_Set with ");
         Write_Int (Int (S.Length));
         Write_Str (" elements:");
         Write_Eol;
         Indent;
         for E of S loop
            Print_Flow_Id (Direct_Mapping_Id (E));
         end loop;
         Outdent;
      else
         Write_Line ("<Empty Node_Set>");
      end if;
   end Print_Node_Set;

   procedure Print_Node_Set (S : Flow_Id_Sets.Set) is
   begin
      if S.Length > 0 then
         Write_Str ("Flow_Id_Set with ");
         Write_Int (Int (S.Length));
         Write_Str (" elements:");
         Write_Eol;
         Indent;
         for F of S loop
            Print_Flow_Id (F);
         end loop;
         Outdent;
      else
         Write_Line ("<Empty Flow_Id_Set>");
      end if;
   end Print_Node_Set;

   procedure Print_Node_Set (S : Ordered_Flow_Id_Sets.Set) is
   begin
      if S.Length > 0 then
         Write_Str ("Ordered_Flow_Id_Set with ");
         Write_Int (Int (S.Length));
         Write_Str (" elements:");
         Write_Eol;
         Indent;
         for F of S loop
            Print_Flow_Id (F);
         end loop;
         Outdent;
      else
         Write_Line ("<Empty Ordered_Flow_Id_Set>");
      end if;
   end Print_Node_Set;

   --------------------
   -- Print_Flow_Map --
   --------------------

   procedure Print_Flow_Map (M : Flow_Id_Maps.Map) is
   begin
      Write_Line ("Flow_Id_Map (with" & M.Length'Img & " elements):");
      Indent;
      for C in M.Iterate loop
         declare
            K : constant Flow_Id          := Flow_Id_Maps.Key (C);
            V : constant Flow_Id_Sets.Set := Flow_Id_Maps.Element (C);
         begin
            Sprint_Flow_Id (K);
            Write_Str (" =>");

            for F of V loop
               Write_Str (" ");
               Sprint_Flow_Id (F);
            end loop;

            Write_Eol;
         end;
      end loop;
      Outdent;
   end Print_Flow_Map;

   --------------------------
   -- Print_Dependency_Map --
   --------------------------

   procedure Print_Dependency_Map (M : Dependency_Maps.Map) is
   begin
      Write_Line ("Dependency_Map:");
      Indent;
      for C in M.Iterate loop
         declare
            A : constant Flow_Id          := Dependency_Maps.Key (C);
            D : constant Flow_Id_Sets.Set := Dependency_Maps.Element (C);
         begin
            Sprint_Flow_Id (A);
            Write_Line (" depends on:");
            Indent;
            for B of D loop
               Print_Flow_Id (B);
            end loop;
            Outdent;
         end;
      end loop;
      Outdent;
   end Print_Dependency_Map;

   ----------------------
   -- Print_Flow_Scope --
   ----------------------

   procedure Print_Flow_Scope (S : Flow_Scope) is
   begin
      if Present (S.Ent) then
         Sprint_Node (S.Ent);
         Write_Str ("|");
         case Valid_Section_T (S.Section) is
            when Spec_Part    => Write_Str ("spec");
            when Private_Part => Write_Str ("priv");
            when Body_Part    => Write_Str ("body");
         end case;
      else
         Write_Str ("null_flow_scope");
      end if;
   end Print_Flow_Scope;

   ------------------------
   -- Sprint_Node_Inline --
   ------------------------

   procedure Sprint_Node_Inline (N : Node_Id) is
   begin
      Temp_String := Null_Unbounded_String;
      Set_Special_Output (Add_To_Temp_String'Access);
      pg (Union_Id (N));
      Cancel_Special_Output;
      Write_Str (To_String (Trim (Temp_String, Ada.Strings.Both)));
   end Sprint_Node_Inline;

   ---------
   -- pfs --
   ---------

   procedure pfs (S : Flow_Scope) is
   begin
      Print_Flow_Scope (S);
      Write_Eol;
   end pfs;

end Flow_Debug;
