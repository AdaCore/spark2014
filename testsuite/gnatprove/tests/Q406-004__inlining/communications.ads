package Communications is

   type Message_Index is mod 16;

   Maximum_Message_Count : constant Integer := Message_Index'Modulus;

   subtype Message_Count is Integer range 0 .. Maximum_Message_Count;
   type Message_Array is array (Message_Index) of Integer;

   protected Mailbox is

      function Item_Count return Message_Count;

      procedure Install_Message (N : in Integer)
        with Post => Item_Count > 0;

      entry Get_Message (N : out Integer);

   private
      Messages : Message_Array := (others => 0);
      Next_In  : Message_Index := Message_Index'First;
      Next_Out : Message_Index := Message_Index'First;
      Count    : Message_Count := 0;
   end Mailbox;

   task type Process;

   Process1, Process2 : Process;

end Communications;
