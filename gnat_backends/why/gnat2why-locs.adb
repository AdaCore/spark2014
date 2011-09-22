------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - L O C S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;                use Atree;
with Namet;                use Namet;
with Sinput;               use Sinput;
with Why.Gen.Names;        use Why.Gen.Names;

package body Gnat2Why.Locs is

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Id
   is

      --  A gnatprove label in Why3 has the following form
      --
      --  #"<filename>" linenumber columnnumber 0# "gnatprove:<VC_Kind>"
      --
      --  The first part, between the #, is a location label, indicating an
      --  Ada source location. The trailing 0 is needed because Why requires
      --  an end column, but we don't need one.
      --  The second part is a text label, which is used here to indicate the
      --  reason for a VC. with prefix the text with "gnatprove:" so that Why3
      --  can easily recognize the label as coming from gnatprove.

      Loc    : constant Source_Ptr := Sloc (N);
      File   : constant String :=
         Get_Name_String (File_Name (Get_Source_File_Index (Loc)));
      Line   : constant Physical_Line_Number := Get_Physical_Line_Number (Loc);
      Column : constant Column_Number := Get_Column_Number (Loc);
      Label : constant String :=
         "#""" & File & """" & Physical_Line_Number'Image (Line) &
         Column_Number'Image (Column) & " 0# " &
         """gnatprove:" & VC_Kind'Image (Reason) & """";
   begin
      return New_Identifier (Label);
   end New_Located_Label;

end Gnat2Why.Locs;
