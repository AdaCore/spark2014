------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                           W H Y - I M A G E S                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2011-2021, AdaCore                     --
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

with Common_Containers; use Common_Containers;
with GNATCOLL.Symbols;  use GNATCOLL.Symbols;
with Outputs;           use Outputs;
with Types;             use Types;
with Uintp;             use Uintp;
with Urealp;            use Urealp;
with Why.Sinfo;         use Why.Sinfo;
with Why.Types;         use Why.Types;

package Why.Images is

   function Can_Be_Printed_In_Decimal_Notation (N : Nat) return Boolean;
   --  Returns whether number N is a multiple of 2 and 5 only. If this is
   --  the case, that means that a fraction whose denominator is a power of
   --  N can be written exactly in decimal notation. Otherwise, the fraction
   --  may not always be written exactly in decimal notation (e.g. 1/3).

   --  Image functions for the basic entities used in Why's AST.
   --  These output the string image into O.

   procedure P (O : Output_Id; Name : Symbol; As_String : Boolean := False);

   procedure P (O : Output_Id; Node : Node_Id);

   procedure P (O : Output_Id; Node : Why_Node_Id);

   procedure P (O : Output_Id; Node : Why_Node_Set);

   procedure P (O : Output_Id; Value : Uint);

   procedure P (O : Output_Id; Value : Ureal);

   procedure P (O : Output_Id; Value : Boolean);

   procedure P (O : Output_Id; Value : EW_Type);

   procedure P (O : Output_Id; Value : EW_Assert_Kind);

   procedure P
     (O      : Output_Id;
      Value  : Source_Ptr;
      Marker : Symbol := No_Symbol);

   procedure P
     (O         : Output_Id;
      Value     : Symbol_Set;
      As_Labels : Boolean := False);

   procedure P
     (O         : Output_Id;
      Value     : String_Sets.Set;
      As_Labels : Boolean := False);

   procedure P
     (O      : Output_Id;
      Value  : EW_Literal;
      Domain : EW_Domain := EW_Prog);

   procedure P (O : Output_Id; Value : EW_Connector);

   procedure P (O : Output_Id; Value : EW_Domain);

   procedure P (O : Output_Id; Value : EW_Subst_Type);

   procedure P (O : Output_Id; Value : EW_Clone_Type);

   procedure P (O : Output_Id;
                Value : EW_Theory_Type;
                Empty_For_Theory : Boolean := False);
   --  Print either "module" or "theory" depending on theory type, if kind is
   --  EW_Theory and Empty_For_Theory is true, print nothing.

   function Img (Name : Symbol) return String;
   --  Return the String represented by the symbol

   function Img (Node : Why_Node_Set) return String;
   --  Return an image of a Node Id (with no leading space)

   function Img (Ty : EW_Type) return String;

end Why.Images;
