------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ E R R O R _ M E S S A G E S            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2014-2015, AdaCore                   --
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

with VC_Kinds; use VC_Kinds;
with Types;    use Types;

package Gnat2Why.Error_Messages is

   type VC_Id is new Integer;

   function Register_VC (N : Node_Id; E : Entity_Id) return VC_Id;
   --  register a VC for entity E, located at node N

   function Has_Registered_VCs return Boolean;
   --  returns true when the function Register_VC has been called

   function To_Tag (Kind : VC_Kind) return String;

   procedure Parse_Why3_Results (S : String);

   procedure Emit_Proof_Result
     (Node       : Node_Id;
      Kind       : VC_Kind;
      Proved     : Boolean;
      E          : Entity_Id;
      Extra_Msg  : String := "";
      Tracefile  : String := "";
      VC_File    : String := "";
      Editor_Cmd : String := "");

end Gnat2Why.Error_Messages;
