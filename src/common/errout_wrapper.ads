with Ada.Containers.Indefinite_Doubly_Linked_Lists;
with Common_Containers; use Common_Containers;
with Errout;
with String_Utils;      use String_Utils;
with Types;             use Types;

package Errout_Wrapper is

   type Msg_Kind is (MK_Error, MK_Warning, MK_Info);

   No_Explain_Code : constant Natural := 0;

   type Message (Len : Natural) is record
      Names         : Node_Lists.List;
      Secondary_Loc : Source_Ptr;
      Explain_Code  : Natural;
      Msg           : String (1 .. Len);
   end record;
   --  Type of a message. Note that this type encapsulates only the string
   --  object, it is different from an error, warning etc.

   No_Message : constant Message :=
     Message'(0, [], No_Location, No_Explain_Code, "");

   package Message_Lists is new Ada.Containers.Indefinite_Doubly_Linked_Lists
     (Message, "=");

   procedure Error_Msg_N
     (Msg           : String;
      N             : Node_Id;
      Kind          : Msg_Kind := MK_Error;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Natural := No_Explain_Code;
      First         : Boolean := False;
      Continuations : String_Lists.List := String_Lists.Empty);
   --  If Names is empty, it is populated with N.

   procedure Error_Msg_N
     (Msg           : Message;
      N             : Node_Id;
      Kind          : Msg_Kind := MK_Error;
      First         : Boolean := False;
      Continuations : Message_Lists.List := Message_Lists.Empty);

   function Create
     (Msg           : String;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Natural := No_Explain_Code) return Message;
   --  Create a Message string. The string may refer to names via & and to a
   --  secondary location via #.

   function Create_N
     (Msg           : String;
      N             : Node_Id := Empty;
      Names         : Name_Id_Lists.List := Name_Id_Lists.Empty;
      Secondary_Loc : Source_Ptr := No_Location;
      Explain_Code  : Natural := No_Explain_Code) return Message;
   --   N is only used for printing of identifiers referred to by & syntax.

   function Compilation_Errors return Boolean
     renames Errout.Compilation_Errors;

   procedure Finalize (Last_Call : Boolean) renames Errout.Finalize;
   --  ??? TODO remove

end Errout_Wrapper;
