------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                               C O N _ I O                                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2016, Altran UK Limited                      --
--                                                                          --
-- sparksmt is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  sparksmt is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  sparksmt;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

--  A helper package to print things on standard output, with SPARK neutral
--  annotations.

package Con_IO with
   SPARK_Mode,
   Annotate => (GNATprove, Always_Return)
is

   procedure New_Line
   with Global => null;
   --  End the current line.

   procedure Put (S : String)
   with Global => null;
   --  Append S to the current line.

   procedure Put (N : Natural)
   with Global => null;
   --  Append N (rendered in decimal) to the current line.

end Con_IO;
