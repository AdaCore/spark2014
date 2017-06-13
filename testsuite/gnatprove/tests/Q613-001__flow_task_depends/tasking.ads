-- This package illustrates support for some of SPARK's tasking features.

package Tasking is

   type Message_Type is (Step, Reset);
   Maximum_Message_Count : constant := 64;
   subtype Message_Index_Type is Positive range 1 .. Maximum_Message_Count;
   subtype Message_Count_Type is Natural range 0 .. Maximum_Message_Count;
   type Message_Array_Type is array(Message_Index_Type) of Message_Type;

   protected Mailbox is
      procedure Send_Message(M : in Message_Type);
      entry Get_Message(M : out Message_Type);

   private
      Next_In   : Message_Index_Type := Message_Index_Type'First;
      Next_Out  : Message_Index_Type := Message_Index_Type'First;
      Count     : Message_Count_Type := 0;
      Non_Empty : Boolean := False;
      Message_Array : Message_Array_Type := (others => Reset);
   end Mailbox;

end Tasking;
