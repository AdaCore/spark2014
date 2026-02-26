------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        E R R O U T _ W R A P P E R                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--              Copyright (C) 2014-2026, Capgemini Engineering              --
--                     Copyright (C) 2014-2026, AdaCore                     --
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

with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Common_Containers;         use Common_Containers;
with Errout;
with Flow_Types;                use Flow_Types;
with GNATCOLL.JSON;             use GNATCOLL.JSON;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with String_Utils;              use String_Utils;
with Types;                     use Types;
with VC_Kinds;                  use VC_Kinds;

package Errout_Wrapper is

   type Msg_Severity is
     (Error_Kind,
      Warning_Kind,
      Info_Kind,
      Low_Check_Kind,
      Medium_Check_Kind,
      High_Check_Kind);

   subtype Check_Kind is Msg_Severity range Low_Check_Kind .. High_Check_Kind;

   --  describes the kinds of messages issued by gnat2why.
   --  * Errors may be issued whenever a SPARK legality issue is encountered.
   --    This will happen only in SPARK checking mode and flow analysis.
   --  * Warnings may be issued for suspicious situations (e.g. unused
   --    statement), or where the tool makes assumptions.
   --  * Info messages are mainly for proved checks
   --  * Check messages are for unproved VCs, and soundness-related flow
   --    analysis messages. Checks come with a priority low, medium or high.

   function To_JSON (Kind : Msg_Severity) return GNATCOLL.JSON.JSON_Value;
   --  Return a JSON object (string) for the message kind

   type Message is record
      Names         : Node_Lists.List;
      Secondary_Loc : Source_Ptr;
      Explain_Code  : Explain_Code_Kind;
      Msg           : Unbounded_String;
   end record;
   --  Type of a message. Note that this type encapsulates only the string
   --  object, it is different from an error, warning etc. The string may
   --  contain & and # characters. & refers to the names in the list of
   --  nodes, while # refers to the location.

   No_Message : constant Message :=
     Message'([], No_Location, EC_None, Null_Unbounded_String);

   package Message_Lists is new
     Ada.Containers.Indefinite_Doubly_Linked_Lists (Message, "=");

   function "&" (M : Message; S : String) return Message;

   type Suppression is (Warning, Check, None);
   type Suppressed_Message (Suppression_Kind : Suppression := None) is record
      case Suppression_Kind is
         when Check =>
            Msg           : String_Id;
            Annot_Kind    : Check_Annotate_Kind;
            Justification : Unbounded_String;

         when others =>
            null;
      end case;
   end record;
   --  When a warning is suppressed, we can store its message; when a check is
   --  suppressed, we can store its message, annotation kind and justification.

   Suppressed_Warning : constant Suppressed_Message :=
     Suppressed_Message'(Suppression_Kind => Warning);
   --  This represents a suppressed warning

   No_Suppressed_Message : constant Suppressed_Message :=
     Suppressed_Message'(Suppression_Kind => None);

   type FPA_Status is (FPA_Unknown, FPA_Gave_Up, FPA_Limit);
   --  Type to represent the status of a failed prover answer
   type Failed_Prover_Answer (Kind : FPA_Status := FPA_Unknown) is record
      case Kind is
         when FPA_Unknown | FPA_Gave_Up =>
            null;

         when FPA_Limit =>
            Timeout : Boolean;
            Step    : Boolean;
            Memory  : Boolean;
      end case;
   end record;
   --  Type to represent the reason for a failed prover answer
   --  (summary for a check)

   FPA_Unknown_Rec : constant Failed_Prover_Answer := (Kind => FPA_Unknown);

   function From_JSON (J : JSON_Value) return Failed_Prover_Answer;
   function To_JSON (FPA : Failed_Prover_Answer) return JSON_Value;

   function To_User_Msg (FPA : Failed_Prover_Answer) return String;
   --  translate FPA into a user-friendly message

   type JSON_Result_Type is record
      Tag           : Unbounded_String;
      Severity      : Msg_Severity;
      Span          : Source_Span;
      E             : Entity_Id := Empty;
      Msg           : Message;
      Details       : Unbounded_String;
      Explanation   : Unbounded_String;
      CE            : Unbounded_String;
      User_Message  : Unbounded_String;
      Fix           : Message := No_Message;
      Continuations : Message_Lists.List;
      Suppr         : Suppressed_Message;
      How_Proved    : Prover_Category := PC_Trivial;
      Tracefile     : Unbounded_String;
      Cntexmp       : Cntexample_Data;
      Check_Tree    : JSON_Value := Create_Object;
      VC_File       : Unbounded_String;
      VC_Loc        : Source_Ptr := No_Location;
      Stats         : Prover_Stat_Maps.Map;
      Unproved_Stat : Failed_Prover_Answer := FPA_Unknown_Rec;
      Editor_Cmd    : Unbounded_String;
   end record
   with
     Predicate =>
       JSON_Result_Type.Tag /= Null_Unbounded_String
       and then JSON_Result_Type.Msg /= No_Message;

   Warnings_Errors : GNATCOLL.JSON.JSON_Array;
   Flow_Msgs       : GNATCOLL.JSON.JSON_Array;
   Proof_Msgs      : GNATCOLL.JSON.JSON_Array;
   --  Variables to hold JSON objects for .spark file output

   type Message_Id is new Integer range -1 .. Integer'Last;
   --  type used to identify a message issued by gnat2why

   No_Message_Id : constant Message_Id := -1;

   function Next_Message_Id return Message_Id;
   --  Return a fresh Message ID

   procedure Add_Json_Msg
     (Msg_List : in out GNATCOLL.JSON.JSON_Array;
      Obj      : JSON_Result_Type;
      Msg_Id   : Message_Id := No_Message_Id);

   function Create
     (Msg           : String;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message;
   --  Create a Message string. The string may refer to names via & and to a
   --  secondary location via #, and it may contain an explain code.

   function Create_N
     (Kind          : Misc_Warning_Kind;
      Extra_Message : String := "";
      Names         : String_Lists.List := String_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message;
   --  Same as Create_N, but intended to produce a warning message, and the
   --  Names are provided in String form.

   procedure Error_Msg_N
     (Msg           : Message;
      N             : Node_Id;
      Kind          : Msg_Severity := Error_Kind;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty;
      Error_Entry   : Boolean := True;
      Tag           : String := "unknown-error");
   --  Issue a message using Kind as the message type. If First is True, locate
   --  the message at the start of the sloc range of the node, otherwise at the
   --  sloc of the node. Continuations are issued at the same location.
   --  If Error_Entry is set, generate an entry in the table of
   --  errors/warnings.

   procedure Error_Msg_N
     (Msg           : String;
      N             : Node_Id;
      Kind          : Msg_Severity := Error_Kind;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : String_Lists.List := String_Lists.Empty);
   --  Same as above, but callers don't need to create a message object.
   --  Instead, the various arguments to Create are provided here along
   --  with the string.

   procedure Error_Msg
     (Msg           : Message;
      Span          : Source_Span;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty;
      Error_Entry   : Boolean := True);
   --  Same as Error_Msg_N but accepts a Source_Span as location

   procedure Error_Msg_N
     (Kind          : Error_Message_Kind;
      N             : Node_Id;
      Msg           : String := "";
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : String_Lists.List := String_Lists.Empty)
   with Pre => Kind not in Unsupported_Kind | Violation_Kind;
   --  Similar to Error_Msg_N, but uses the Error_Kind to generate the
   --  message text.

   --  TODO overload with other warning kinds (VC and flow)

   procedure Warning_Msg_N
     (Kind          : Misc_Warning_Kind;
      N             : Node_Id;
      Extra_Message : String := "";
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Similar to Error_Msg_N, but uses the Warning_Kind to generate the
   --  message text. The Extra_Message is appended to the warning message text.
   --  This function also handles warning suppression and promotion to error
   --  (-W, -A, -D switches, and --pedantic).

   procedure Warning_Msg_N
     (Kind          : Misc_Warning_Kind;
      N             : Node_Id;
      Msg           : Message;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Variant of Warning_Msg_N where the user creates the message object,
   --  ideally with the Create_N that takes a Misc_Warning_Kind.

   function Warning_Is_Suppressed
     (N   : Node_Id;
      Msg : String;
      F1  : Flow_Id := Null_Flow_Id;
      F2  : Flow_Id := Null_Flow_Id;
      F3  : Flow_Id := Null_Flow_Id) return String_Id;
   --  Check if the warning for the given node, message and flow id is
   --  suppressed. If the function returns No_String, the warning is not
   --  suppressed. If it returns Null_String_Id the warning is suppressed,
   --  but no reason has been given. Otherwise, the String_Id of the reason
   --  is provided.

   function Tag_Suffix (Kind : Misc_Warning_Kind) return String;
   --  If the option is set to print the tag for each warning message, then
   --  this function returns the string " [tag]" (note the initial space),
   --  where "tag" is the tag name of the warning kind.
   --  If not, it returns the empty string.

   function Escape (S : String) return String;
   --  Escape the special characters # and & in the error message

   function Compilation_Errors return Boolean
   renames Errout.Compilation_Errors;

   procedure Finalize (Last_Call : Boolean) renames Errout.Finalize;
   --  ??? TODO remove

end Errout_Wrapper;
