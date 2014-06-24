------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W _ D E B U G                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013-2014, Altran UK Limited              --
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

with Atree;  use Atree;
with Types;  use Types;

with Output; use Output;
with Sprint; use Sprint;

with Ada.Containers;

use type Ada.Containers.Count_Type;

package body Flow_Debug is

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
      Write_Str ("Flow_Id_Set with ");
      Write_Int (Int (S.Length));
      Write_Str (" elements:");
      Write_Eol;
      Indent;
      for F of S loop
         Print_Flow_Id (F);
      end loop;
      Outdent;
   end Print_Node_Set;

   procedure Print_Node_Set (S : Ordered_Flow_Id_Sets.Set) is
   begin
      Write_Str ("Ordered_Flow_Id_Set with ");
      Write_Int (Int (S.Length));
      Write_Str (" elements:");
      Write_Eol;
      Indent;
      for F of S loop
         Print_Flow_Id (F);
      end loop;
      Outdent;
   end Print_Node_Set;

   --------------------------
   -- Print_Dependency_Map --
   --------------------------

   procedure Print_Dependency_Map (M : Dependency_Maps.Map) is
   begin
      Write_Str ("Dependency_Map:");
      Write_Eol;
      Indent;
      for C in M.Iterate loop
         declare
            A : constant Flow_Id          := Dependency_Maps.Key (C);
            D : constant Flow_Id_Sets.Set := Dependency_Maps.Element (C);
         begin
            Sprint_Flow_Id (A);
            Write_Str (" depends on:");
            Write_Eol;
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

   procedure Print_Flow_Scope (S : Flow_Scope)
   is
   begin
      if Present (S.Pkg) then
         Sprint_Node (S.Pkg);
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

   ---------
   -- pfs --
   ---------

   procedure pfs (S : Flow_Scope)
   is
   begin
      Print_Flow_Scope (S);
      Write_Eol;
   end pfs;

end Flow_Debug;
