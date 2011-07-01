------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                          E X P L A N A T I O N S                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with System.OS_Lib;     use System.OS_Lib;
with VC_Kinds;          use VC_Kinds;

package Explanations is

   type Explanation is private;

   function Get_VC_Explanation (Expl_File : String) return Explanation;
   --  Parse an explanation file to return an explanation.

   procedure Print_Error_Msg (X : Explanation; Proved : Boolean := False);
   --  Print an error message corresponding to the explanation in argument.

private

   type Explanation is
   record
      EX_Filename : String_Access;
      EX_Line     : String_Access;
      EX_Col      : String_Access;
      EX_Kind     : VC_Kind := VC_Unused;
   end record;

end Explanations;
