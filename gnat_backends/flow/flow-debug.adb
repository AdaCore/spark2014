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
with Treepr; use Treepr;

package body Flow.Debug is

   ----------------------
   --  Print_Node_Set  --
   ----------------------

   procedure Print_Node_Set (S : Node_Sets.Set)
   is
   begin
      Write_Str ("Node_Set with ");
      Write_Int (Int (S.Length));
      Write_Str (" elements:");
      Write_Eol;
      Indent;
      for N of S loop
         Print_Node_Briefly (N);
      end loop;
      Outdent;
   end Print_Node_Set;

end Flow.Debug;
