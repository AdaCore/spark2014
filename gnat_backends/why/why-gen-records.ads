------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
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

with Types;     use Types;
with Why.Ids;   use Why.Ids;
with Why.Inter; use Why.Inter;
with Why.Sinfo; use Why.Sinfo;

package Why.Gen.Records is
   --  This package encapsulates the encoding of Ada records into Why.

   procedure Declare_Ada_Record
     (File    : in out Why_File;
      Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id);

   function New_Ada_Record_Access
     (Ada_Node : Node_Id;
      Domain : EW_Domain;
      Name   : W_Expr_Id;
      Field  : Entity_Id) return W_Expr_Id;

end Why.Gen.Records;
