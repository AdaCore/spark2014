------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
-- F L O W . G E N E R A T E D _ G L O B A L S . P H A S E _ 1 . W R I T E  --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                Copyright (C) 2018-2020, Altran UK Limited                --
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

with Common_Iterators; use Common_Iterators;
with Elists;           use Elists;
with Lib.Util;         use Lib.Util;
with Sem_Util;         use Sem_Util;
with Stand;            use Stand;

package body Flow_Generated_Globals.Phase_1.Write is

   -----------------
   -- New_GG_Line --
   -----------------

   procedure New_GG_Line (K : ALI_Entry_Kind) is
   begin
      Write_Info_Str ("GG ");
      Write_Info_Str (K'Img);
   end New_GG_Line;

   ---------------
   -- Serialize --
   ---------------

   procedure Serialize (E : Entity_Id) is
   begin
      Write_Info_Char (' ');
      Write_Info_Str (if E = Standard_Standard
                      then "__standard"
                      else Unique_Name (E));
      --  ??? the __standard is also special cased in phase 2; this should be
      --  done in one place only.
   end Serialize;

   procedure Serialize (N : Int) is
   begin
      --  Directly use the frontend API for writing integers, as this seems
      --  simpler than instantiating the generic serializer for discrete types.
      Write_Info_Char (' ');
      Write_Info_Int (N);
   end Serialize;

   procedure Serialize (S : String) is
   begin
      Write_Info_Char (' ');
      Write_Info_Str (S);
   end Serialize;

   procedure Serialize (Nodes : Node_Lists.List; Label : String := "") is
   begin
      if Label /= "" then
         Serialize (Label);
      end if;

      Serialize (Int (Nodes.Length));

      for E of Nodes loop
         Serialize (E);
      end loop;
   end Serialize;

   procedure Serialize (Nodes : Node_Sets.Set; Label : String := "") is
   begin
      if Label /= "" then
         Serialize (Label);
      end if;

      Serialize (Int (Nodes.Length));

      for E of Nodes loop
         Serialize (E);
      end loop;
   end Serialize;

   procedure Serialize (L : Elist_Id) is
   begin
      Serialize (List_Length (L));

      for E of Iter (L) loop
         Serialize (E);
      end loop;
   end Serialize;

   ------------------------
   -- Serialize_Discrete --
   ------------------------

   procedure Serialize_Discrete (A : T; Label : String := "") is
   begin
      if Label /= "" then
         Serialize (Label);
      end if;

      Serialize (A'Img);
   end Serialize_Discrete;

   -----------------------
   -- Terminate_GG_Line --
   -----------------------

   procedure Terminate_GG_Line is
   begin
      Write_Info_Terminate;
   end Terminate_GG_Line;

end Flow_Generated_Globals.Phase_1.Write;
