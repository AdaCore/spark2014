------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           W H Y - I M A G E S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2011, AdaCore                        --
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

with Namet;     use Namet;
with Uintp;     use Uintp;
with Urealp;    use Urealp;
with Why.Types; use Why.Types;
with Why.Sinfo; use Why.Sinfo;
with Outputs;   use Outputs;

package Why.Images is
   --  Image functions for the basic entities used in Why's AST.
   --  These output the string image into O.

   procedure P (O : Output_Id; Name : Name_Id);

   procedure P (O : Output_Id; Node : Why_Node_Id);

   procedure P (O : Output_Id; Value : Uint);

   procedure P (O : Output_Id; Value : Ureal);

   procedure P (O : Output_Id; Value : Boolean);

   procedure P (O : Output_Id; Value : EW_Base_Type);

   procedure P
     (O      : Output_Id;
      Value  : EW_Literal;
      Domain : EW_Domain := EW_Prog);

   procedure P
     (O       : Output_Id;
      Value   : EW_Binary_Op;
      Op_Type : EW_Scalar := EW_Int);

   procedure P (O : Output_Id; Value : EW_Relation);

   procedure P (O : Output_Id; Value : EW_Connector);

   procedure P (O : Output_Id; Value : EW_Unary_Op);

   procedure P (O : Output_Id; Value : EW_Domain);

   function Img (Name : Name_Id) return String;
   --  Return the String content of Name

   function Img (Node : Why_Node_Id) return String;
   --  Return an image of a Node Id (with no leading space)

end Why.Images;
