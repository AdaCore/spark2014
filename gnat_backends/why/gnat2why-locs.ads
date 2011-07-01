------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - L O C S                           --
--                                                                          --
--                                 S p e c                                  --
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

with Outputs;   use Outputs;
with Types;     use Types;
with Why.Ids;   use Why.Ids;
with VC_Kinds;  use VC_Kinds;

package Gnat2Why.Locs is

   --  The purpose of this package is to track source locations of Ada code
   --  through the Why machinery.
   --
   --  Using this package, one can create named labels, that are fresh
   --  each time the function New_Located_Label is called. Such a label can
   --  then be used for example to name predicates in VCs.
   --
   --  Using the function Print_Label_List, all labels are then printed to a
   --  file that can be passed to Why using the --locs option.
   --
   --  With the options --multi-why and --explain, Why generates, for each VC,
   --  a file .why containing the VC, and a file .xpl containing the
   --  information attached to the label that belongs to the VC. This
   --  information contains at least the original source location and the kind
   --  of the VC. The kind is one of the following:
   --    * Other
   --    * Absurd
   --    * Assert
   --    * Check
   --    * Pre
   --    * Post
   --    * WfRel
   --    * VarDecr
   --    * LoopInvInit
   --    * LoopInvPreserv
   --    * Lemma

   function New_Located_Label (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Id;
   --  Generate a label for the given Ada node.
   --
   --  This means: associate a fresh Why Identifier to the source location of
   --  the Ada Node, and return the identifier.

   procedure Print_Locations_Table (O : Output_Id);
   --  Print the list of entries in the location table in a format suitable
   --  for Why.

   procedure Print_Label_List (O : Output_Id := Stdout);
   --  Print the list of labels in the location table
end Gnat2Why.Locs;
