------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                Copyright (C) 2013-2022, Altran UK Limited                --
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

with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Flow;                      use Flow;
with Flow_Types;                use Flow_Types;
with GNATCOLL.JSON;             use GNATCOLL.JSON;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with SPARK_Util;                use SPARK_Util;
with Types;                     use Types;
with VC_Kinds;                  use VC_Kinds;

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

   type Session_Dir_Base_ID is new Natural;

   subtype Session_Dir_ID is Session_Dir_Base_ID
   range 1 .. Session_Dir_Base_ID'Last;
   --  Indices for session files

   No_Session_Dir : constant Session_Dir_Base_ID := 0;

   type Suppression is (Warning, Check, None);

   type Suppressed_Message (Suppression_Kind : Suppression := None) is record
      case Suppression_Kind is
         when Warning | Check =>
            Msg : String_Id;
            case Suppression_Kind is
               when Check =>
                  Annot_Kind    : Annotate_Kind;
                  Justification : Unbounded_String;
               when others =>
                  null;
            end case;
         when others =>
            null;
      end case;
   end record;
   --  When a warning is suppressed, we can store its message; when a check is
   --  suppressed, we can store its message, annotation kind and justification.

   Suppressed_Warning : constant Suppressed_Message :=
     Suppressed_Message'(Suppression_Kind => Warning, Msg => First_String_Id);
   --  This represents a suppressed warning. We don't care about its content,
   --  because suppressed warnings are not reported.

   No_Suppressed_Message : constant Suppressed_Message :=
     Suppressed_Message'(Suppression_Kind => None);

   function Register_Session_Dir (S : String) return Session_Dir_ID;
   --  Register a string as a session file, create its ID and return it.

   function Get_Flow_JSON return JSON_Array;
   function Get_Proof_JSON return JSON_Array;
   function Get_Session_Map_JSON return JSON_Value;
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
      Details      : String        := "";
      Fix          : String        := "";
      Severity     : Msg_Severity;
      N            : Node_Id;
      Suppressed   : out Boolean;
      F1           : Flow_Id       := Null_Flow_Id;
      F2           : Flow_Id       := Null_Flow_Id;
      F3           : Flow_Id       := Null_Flow_Id;
      FF1          : Flow_Id       := Null_Flow_Id;
      FF2          : Flow_Id       := Null_Flow_Id;
      Tag          : Flow_Tag_Kind := Empty_Tag;
      SRM_Ref      : String        := "";
      Tracefile    : String        := "";
      Continuation : Boolean       := False)
   with Pre => (if Present (F2) then Present (F1))
     and then (if Present (F3) then Present (F2))
     and then (if Present (FF2) then Present (FF1))
     and then (if Continuation
               then Tracefile = "" and then Details = "" and then Fix = "")
     and then (if Severity in Check_Kind then Tag in Valid_Flow_Tag_Kind)
     and then (case Tag is
                 when Empty_Tag =>
                   True,
                 when Flow_Error_Kind =>
                   Severity = Error_Kind,
                 when Flow_Check_Kind =>
                   Severity in Check_Kind | Info_Kind,
                 when Flow_Warning_Kind =>
                   Severity = Warning_Kind);
   --  Output a message attached to the given node with a substitution
   --  using F1, F2 and F3. If not empty, the details and possible fix for the
   --  check are appended to the message with a substitution for Fix using FF1
   --  and FF2. It also adds a JSON entry in the "unit.flow" file for the given
   --  entity E.
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
      Details      : String                := "";
      Fix          : String                := "";
      Severity     : Msg_Severity;
      N            : Node_Id;
      F1           : Flow_Id               := Null_Flow_Id;
      F2           : Flow_Id               := Null_Flow_Id;
      F3           : Flow_Id               := Null_Flow_Id;
      FF1          : Flow_Id               := Null_Flow_Id;
      FF2          : Flow_Id               := Null_Flow_Id;
      Tag          : Flow_Tag_Kind         := Empty_Tag;
      SRM_Ref      : String                := "";
      Path         : Vertex_Sets.Set       := Vertex_Sets.Empty_Set;
      Vertex       : Flow_Graphs.Vertex_Id := Flow_Graphs.Null_Vertex;
      Continuation : Boolean               := False)
   with Pre => (if Present (F2) then Present (F1))
     and then (if Present (F3) then Present (F2))
     and then (if Present (FF2) then Present (FF1))
     and then (if Continuation
               then Path.Is_Empty and then Details = "" and then Fix = "")
     and then (if Severity in Check_Kind then Tag in Valid_Flow_Tag_Kind)
     and then (case Tag is
                 when Empty_Tag =>
                   True,
                 when Flow_Error_Kind =>
                   Severity = Error_Kind,
                 when Flow_Check_Kind =>
                   Severity in Check_Kind | Info_Kind,
                 when Flow_Warning_Kind =>
                   Severity = Warning_Kind);
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
      Cntexmp     : JSON_Value;
      Verdict     : Cntexmp_Verdict;
      Check_Tree  : JSON_Value;
      VC_File     : String;
      VC_Loc      : Node_Id;
      Editor_Cmd  : String;
      Explanation : String;
      E           : Entity_Id;
      How_Proved  : Prover_Category;
      SD_Id       : Session_Dir_Base_ID;
      Stats       : Prover_Stat_Maps.Map;
      Place_First : Boolean;
      Check_Info  : Check_Info_Type);
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
   --        - "@X": Value at label X
   --        - "error_message": The model element represents error message, not
   --          source-code element. The error message is saved in the name of
   --          the model element.
   --        - "before_loop": Value of the reference before entering the loop
   --        - "current_iteration": Value in the current iteration
   --        - "previous_iteration": Value in the previous iteration
   --        - "other"
   --  @param Verdict result of the counterexample checking
   --  @param VC_File if the VC is a manual proof, the VC file for manual proof
   --  @param VC_Loc is the location of the verification check as opposed to
   --  parameter N which contains the location of the first failing part of a
   --  VC (raised as location for messages).
   --  @param Editor_Cmd the editor command to spawn manual prover
   --  @param Explanation an optional string ("" if absent) explaining the
   --    reason for the failing check
   --  @param E which subprogram this VC belongs to
   --  @param How_Proved which prover or analysis discharged this VC
   --  @param Stats describes which provers and which timeout/steps where
   --    necessary
   --  @param Place_First signal if placement on the beginning of the
   --         expression should be used (instead of the middle)
   --  @param Check_Info extra information for the check

end Flow_Error_Messages;
