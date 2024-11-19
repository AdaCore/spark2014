with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Common_Containers;   use Common_Containers;
with Errout;
with GNATCOLL.JSON;
with String_Utils;        use String_Utils;
with Types;               use Types;
with VC_Kinds;            use VC_Kinds;

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

   type Message (Len : Natural) is record
      Names         : Node_Lists.List;
      Secondary_Loc : Source_Ptr;
      Explain_Code  : Explain_Code_Kind;
      Msg           : String (1 .. Len);
   end record;
   --  Type of a message. Note that this type encapsulates only the string
   --  object, it is different from an error, warning etc. The string may
   --  contain & and # characters. & refers to the names in the list of
   --  nodes, while # refers to the location.

   No_Message : constant Message := Message'(0, [], No_Location, EC_None, "");

   package Message_Lists is new Ada.Containers.Indefinite_Doubly_Linked_Lists
     (Message, "=");

   function Create
     (Msg           : String;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message;
   --  Create a Message string. The string may refer to names via & and to a
   --  secondary location via #, and it may contain an explain code.

   function Create_N
     (Msg           : String;
      Names         : String_Lists.List := String_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Explain_Code_Kind := EC_None) return Message;
   --  Same as Create, but the names can be provided as a list of Name_Ids.
   --  The node N is only used to help pretty-printing the names (it is used to
   --  derive casing information).

   procedure Error_Msg_N
     (Msg           : Message;
      N             : Node_Id;
      Kind          : Msg_Severity := Error_Kind;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Issue a message using Kind as the message type. If First is True, locate
   --  the message at the start of the sloc range of the node, otherwise at the
   --  sloc of the node. Continuations are issued at the same location.

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
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Same as Error_Msg_N but accepts a Source_Span as location

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
   --  Similar to Error_Msg_N,

   function Escape (S : String) return String;
   --  Escape the special characters # and & in the error message

   function Compilation_Errors return Boolean
     renames Errout.Compilation_Errors;

   procedure Finalize (Last_Call : Boolean) renames Errout.Finalize;
   --  ??? TODO remove

end Errout_Wrapper;
