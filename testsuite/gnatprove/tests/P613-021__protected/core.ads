pragma Profile(Jorvik);
pragma Partition_Elaboration_Policy(Sequential);
pragma SPARK_Mode(On);

package Core is

   ---------------------------------------------------------------------------------------
   -- The declarations below are only needed to support the private section of the mailbox

   Maximum_Message_Count : constant := 16;
   type Message_Index is mod Maximum_Message_Count;
   subtype Message_Count is Integer range 0 .. Maximum_Message_Count;
   type Message_Record is
      record
         Value : Integer;
         Size  : Natural;
      end record;
   type Message_Array is array(Message_Index) of Message_Record;

   -- The declarations above are only needed to support the private section of the mailbox
   ---------------------------------------------------------------------------------------

   protected Mailbox is

      -- Used only in contracts, but can't be made Ghost because of the protected type.
      function Item_Count return Message_Count
        with Global => null;

      procedure Install_Message(N : in Integer)
        with Post => Item_Count > 0;

      -- Retrieve a message from this mailbox.
      entry Get_Message(N : out Integer);
        -- with Pre => Item_Count > 0;

   private
      Messages : Message_Array :=
        (others => (Value => 0, Size => 0));
      Next_In  : Message_Index := Message_Index'First;
      Next_Out : Message_Index := Message_Index'First;
      Count    : Message_Count := 0;
   end Mailbox;


end Core;
