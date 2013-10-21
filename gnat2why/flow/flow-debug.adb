------------------------------------------------------------------------------
--                                                                          --
--                           GNAT2WHY COMPONENTS                            --
--                                                                          --
--                           F L O W . D E B U G                            --
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

with Output; use Output;

package body Flow.Debug is

   --------------------
   -- Print_Node_Set --
   --------------------

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
               Sprint_Flow_Id (B);
               Write_Eol;
            end loop;
            Outdent;
         end;
      end loop;
      Outdent;
   end Print_Dependency_Map;

   procedure Print_Optional_Dependency_Map (M : Optional_Dependency_Maps.Map)
   is
      use type Ada.Containers.Count_Type;
      use Optional_Dependency_Maps;
   begin
      Write_Str ("Optional_Dependency_Map:");
      Write_Eol;
      Indent;
      if M.Length >= 1 then
         for C in M.Iterate loop
            declare
               A : constant Flow_Id              := Key (C);
               D : constant Optional_Flow_Id_Set := Element (C);
            begin
               Sprint_Flow_Id (A);
               if D.Exists then
                  Write_Str (" depends on:");
                  Write_Eol;
                  Indent;
                  for B of D.The_Set loop
                     Sprint_Flow_Id (B);
                     Write_Eol;
                  end loop;
                  Outdent;
               else
                  Write_Eol;
               end if;
            end;
         end loop;
      else
         Write_Str ("null");
         Write_Eol;
      end if;
      Outdent;
   end Print_Optional_Dependency_Map;

end Flow.Debug;
