------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2019, Altran UK Limited                --
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

with Flow;          use Flow;
with Flow_Types;    use Flow_Types;
with GNATCOLL.JSON; use GNATCOLL.JSON;
with Types;         use Types;
with VC_Kinds;      use VC_Kinds;

package Flow_Error_Messages is

   type Msg_Severity is
     (Error_Kind,
      High_Check_Kind,
      Medium_Check_Kind,
      Low_Check_Kind,
      Warning_Kind,
      Info_Kind);

   subtype Check_Kind is Msg_Severity range High_Check_Kind .. Low_Check_Kind;

   --  describes the kinds of messages issued by gnat2why.
   --  * Errors may be issued whenever a SPARK legality issue is encountered.
   --    This will happen only in SPARK checking mode and flow analysis.
   --  * Warnings may be issued for suspicious situations (e.g. unused
   --    statement), or where the tool makes assumptions.
   --  * Info messages are mainly for proved checks
   --  * Check messages are for unproved VCs, and soundness-related flow
   --    analysis messages. Checks come with a priority low, medium or high.

   Found_Flow_Error : Boolean := False;

   --  This boolean becomes True if we find a error during flow analysis which
   --  should stop further analysis (i.e. proof).

   function Get_Flow_JSON return JSON_Array;
   function Get_Proof_JSON return JSON_Array;
   --  Call these functions to get the messages of proof and flow in JSON form.
   --  Should be called only when analysis is finished.

   function Fresh_Trace_File return String;
   --  Returns a name for a trace file. This name should be unique for the
   --  project.

   function Error_Location (G : Flow_Graphs.Graph;
                            M : Attribute_Maps.Map;
                            V : Flow_Graphs.Vertex_Id)
                            return Node_Or_Entity_Id;
   --  Find a good place to raise an error for vertex V

   procedure Error_Msg_Flow
     (E            : Entity_Id;
      Msg          : String;
      Severity     : Msg_Severity;
      N            : Node_Id;
      Suppressed   : out Boolean;
      F1           : Flow_Id       := Null_Flow_Id;
      F2           : Flow_Id       := Null_Flow_Id;
      F3           : Flow_Id       := Null_Flow_Id;
      Tag          : Flow_Tag_Kind := Empty_Tag;
      SRM_Ref      : String        := "";
      Tracefile    : String        := "";
      Continuation : Boolean       := False)
   with Pre => (if Present (F2) then Present (F1))
                and then (if Present (F3) then Present (F2))
                and then (if Continuation then Tracefile = "");
   --  Output a message attached to the given node with a substitution
   --  using F1, F2 and F3. It also adds a JSON entry in the "unit.flow" file
   --  for the given entity E.
   --
   --  The substitution characters used are slightly different from the
   --  standard GNAT ones defined in Errout.
   --  * Use & or % as the substitution characters, which quote the flow id
   --    with or without double quotes respectively.
   --  * Use # to insert both the quoted name of the entity, and a line
   --    reference.
   --  * Use @ to insert the sloc of the entity.
   --
   --  SRM_Ref should be a pointer into the SPARK RM. For example:
   --     "1.2.3(4)"

   procedure Error_Msg_Flow
     (FA           : in out Flow_Analysis_Graphs;
      Msg          : String;
      Severity     : Msg_Severity;
      N            : Node_Id;
      F1           : Flow_Id               := Null_Flow_Id;
      F2           : Flow_Id               := Null_Flow_Id;
      F3           : Flow_Id               := Null_Flow_Id;
      Tag          : Flow_Tag_Kind         := Empty_Tag;
      SRM_Ref      : String                := "";
      Path         : Vertex_Sets.Set       := Vertex_Sets.Empty_Set;
      Vertex       : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      Continuation : Boolean               := False)
   with Pre => (if Present (F2) then Present (F1))
                and then (if Present (F3) then Present (F2))
                and then (if Continuation then Path.Is_Empty);
   --  As above but it also writes the tracefile.
   --
   --  Also:
   --
   --  E is worked out from FA, and FA.No_Errors_Or_Warnings is
   --  appropriately modified.
   --
   --  Instead of the Tracefile parameter we have the Path which contains the
   --  vertices we want to write to the tracefile.
   --
   --  Finally, for debug purposes, Vertex should be set to the vertex
   --  where the error was detected. This is printed in debug mode.

   procedure Error_Msg_Proof
     (N           : Node_Id;
      Msg         : String;
      Is_Proved   : Boolean;
      Tag         : VC_Kind;
      Tracefile   : String;
      Cntexmp     : JSON_Value;
      Check_Tree  : JSON_Value;
      VC_File     : String;
      VC_Loc      : Node_Id;
      Editor_Cmd  : String;
      E           : Entity_Id;
      How_Proved  : Prover_Category;
      Stats       : Prover_Stat_Maps.Map;
      Place_First : Boolean);
   --  register a message for proof (i.e. which corresponds to a check that is
   --  usually taken care of by proof)
   --  @param N the node on which this VC is placed
   --  @param Msg the message string
   --  @param Tag the kind of VC
   --  @param Tracefile the tracefile of the VC which describes context
   --  @param Cntexmp counterexample model; JSON object describing values of
   --    counterexample elements:
   --      - fields of this object correspond to file names
   --      - values of the fields correspond to line numbers
   --      - line number is JSON array (list) of counterexample elements
   --      - counterexample element is JSON object with fields "name",
   --        "value", and "kind"
   --      - field "kind" can have one of the following values:
   --        - "result": Result of a function call
   --        - "old": Old value of function argument
   --        - "error_message": The model element represents error message, not
   --          source-code element. The error message is saved in the name of
   --          the model element.
   --        - "other"
   --  @param VC_File if the VC is a manual proof, the VC file for manual proof
   --  @param VC_Loc is the location of the verification check as opposed to
   --  parameter N which contains the location of the first failing part of a
   --  VC (raised as location for messages).
   --  @param Editor_Cmd the editor command to spawn manual prover
   --  @param E which subprogram this VC belongs to
   --  @param How_Proved which prover or analysis discharged this VC
   --  @param Stats describes which provers and which timeout/steps where
   --    necessary
   --  @param Place_First signal if placement on the beginning of the
   --         expression should be used (instead of the middle)

end Flow_Error_Messages;
