------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - A N N O T A T E                   --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2014, AdaCore                     --
--                     Copyright (C) 2014, Altran UK Limited                --
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

with SPARK_Util; use SPARK_Util;
with Types;      use Types;

package Gnat2Why.Annotate is

   --  This package deals with justification of individual messages using
   --  pragma Annotate.

   --  The user can suppress check messages emitted by gnatprove by putting a
   --  pragma Annotate in the source code. An example is the following:

   --    return (X + Y) / (X - Y);
   --    pragma Annotate (Gnatprove, False_Positive,
   --                     "divide by zero", "reviewed by John Smith");

   --  The pragma hasa the following form:
   --    pragma Annotate (Gnatprove, Category, Pattern, Reason);

   --  where
   --    Gnatprove   is fixed
   --    Category    is one of False_Positive or Intentional
   --    Pattern     is a string literal describing the pattern of the messages
   --                which shall be suppressed
   --    Reason      is a string literal providing a reason for the
   --                suppression.

   --  All arguments should be provided.

   --  The category has no impact on the behavior of the tool, but the idea
   --  is that False_Positive should be used to suppress checks that cannot
   --  occcur, but Gnatprove was unable to detect this; Intentional indicates
   --  that the condition can occure but is not considered to be a bug.

   --  Pattern should be a substring of the Gnatprove check message to be
   --  suppressed.

   --  Reason is any string that the user can use to provide a reason for the
   --  suppression. This reason may be present in a Gnatprove report.

   --  Placement rules are as follows: in a statement
   --  list or declaration list, pragma Annotate applies to the preceding item
   --  in the list, ignoring other pragma Annotate. If there is no preceding
   --  item, the pragma applies to the enclosing entity.

   procedure Mark_Pragma_Annotate
     (N         : Node_Id;
      Preceding : Node_Id)
     with Pre => Is_Pragma_Annotate_Gnatprove (N);
   --  Call this procedure to register a pragma Annotate

   type Annotate_Kind is (Intentional, False_Positive);

   type Annotated_Range is record
      Kind    : Annotate_Kind;
      Pattern : String_Id;
      Reason  : String_Id;
      First   : Source_Ptr;
      Last    : Source_Ptr;
   end record;

   procedure Check_Is_Annotated
     (Node  : Node_Id;
      Msg   : String;
      Found : out Boolean;
      Info  : out Annotated_Range);
   --  for a given node and message string, search if there is a pragma
   --  Annotate which applies to the message for this node. If so, set Found to
   --  True and fill in the Info record. Otherwise, Found is set to False and
   --  Info is uninitialized

end Gnat2Why.Annotate;
