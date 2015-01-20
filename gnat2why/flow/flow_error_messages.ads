------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2013-2015, Altran UK Limited              --
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

--  This package provides mechanisms for emitting errors and warnings.

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Flow;                  use Flow;
with Flow_Types;            use Flow_Types;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with Types;                 use Types;

with VC_Kinds;              use VC_Kinds;

package Flow_Error_Messages is

   type Msg_Kind is
     (Error_Kind,
      Warning_Kind,
      Info_Kind,
      High_Check_Kind,
      Medium_Check_Kind,
      Low_Check_Kind);

   subtype Check_Kind is Msg_Kind range High_Check_Kind .. Low_Check_Kind;

   --  describes the kinds of messages issued by gnat2why.
   --  * Errors may be issued whenever a SPARK legality issue is encountered.
   --    This will happen only in SPARK checking mode and flow analysis.
   --  * Warnings may be issued for suspicious situations (e.g. unused
   --    statement), or where the tool makes assumptions.
   --  * Info messages are mainly for proved checks
   --  * check messages are for unproved VCs, and soundness-related flow
   --    analysis messages. Checks come with a priority low, medium or high.

   Found_Flow_Error : Boolean := False;

   --  This boolean becomes True if we find a error during flow analysis which
   --  should stop further analysis (i.e. proof).

   function Get_Flow_JSON return JSON_Array;
   function Get_Proof_JSON return JSON_Array;
   --  Call these functions to get the messages of proof and flow in JSON form.
   --  Should be called only when analysis is finished

   function Fresh_Trace_File return String;
   --  Returns a name for a trace file. This name should be unique for the
   --  project.

   procedure Error_Msg_Flow
     (E          : Entity_Id;
      Msg        : String;
      Kind       : Msg_Kind;
      N          : Node_Id;
      Suppressed : out Boolean;
      F1         : Flow_Id       := Null_Flow_Id;
      F2         : Flow_Id       := Null_Flow_Id;
      F3         : Flow_Id       := Null_Flow_Id;
      Tag        : Flow_Tag_Kind := Empty_Tag;
      SRM_Ref    : String        := "";
      Tracefile  : String        := "")
   with Pre => (if Present (F2) then Present (F1)) and
               (if Present (F3) then Present (F2));
   --  Output a message attached to the given node with a substitution
   --  using F1 and F2. It also adds a JSON entry in the "unit.flow" file
   --  for the given entity E.
   --
   --  The substitution characters used are slightly different from the
   --  standard GNAT ones defined in Errout.
   --  * Use & or % as the substitution characters, which quote the flow id
   --    with or without double quotes respectively.
   --  * Use # to insert both the quoted name of the entity, and a line
   --    reference.
   --
   --  SRM_Ref should be a pointer into the SPARK RM. For example:
   --     "1.2.3(4)"

   procedure Error_Msg_Flow
     (FA        : in out Flow_Analysis_Graphs;
      Msg       : String;
      Kind      : Msg_Kind;
      N         : Node_Id;
      F1        : Flow_Id               := Null_Flow_Id;
      F2        : Flow_Id               := Null_Flow_Id;
      F3        : Flow_Id               := Null_Flow_Id;
      Tag       : Flow_Tag_Kind         := Empty_Tag;
      SRM_Ref   : String                := "";
      Tracefile : String                := "";
      Vertex    : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex)
   with Pre => (if Present (F2) then Present (F1)) and
               (if Present (F3) then Present (F2));
   --  As above, but:
   --
   --  E is worked out from FA, and FA.No_Errors_Or_Warnings is
   --  appropriately modified.
   --
   --  Finally, for debug purposes, Vertex should be set to the vertex
   --  where the error was detected. This is printed in debug mode.

   procedure Error_Msg_Proof
     (N           : Node_Id;
      Msg         : String;
      Is_Proved   : Boolean;
      Tag         : String;
      Tracefile   : String;
      VC_File     : String;
      Editor_Cmd  : String;
      E           : Entity_Id;
      Place_First : Boolean);
   --  !!! documentation needed

end Flow_Error_Messages;
