-- The 1553 bus interface.
-- The missile manager is a bus controller (BC); all
-- other system components are on the bus as remote
-- terminals (RTs).
--  R messages go BC -> RT
--  T messages go RT -> BC
--
-- $Id: bus.ads,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: bus.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.7  2003/06/25 20:26:41  adi
-- Added base type assertion
--
-- Revision 1.6  2003/02/12 21:09:38  adi
-- Added Set_X_Message_Valid public functions and the Show
-- debugging functions
--
-- Revision 1.5  2003/02/11 20:13:06  adi
-- Added valid and fresh checking functions
--
-- Revision 1.4  2003/02/05 22:42:10  adi
-- Improved typing for RTC proof
--
-- Revision 1.3  2003/02/03 23:15:07  adi
-- Added Acknowledge functions
--
-- Revision 1.2  2003/02/03 19:47:15  adi
-- Made it easier to test
--
-- Revision 1.1  2003/02/03 18:13:16  adi
-- Initial revision
--
--
with SystemTypes;
--# inherit SystemTypes;
package Bus
  --# own Inputs, Outputs;
  --# initializes Inputs, Outputs;
is
   -- Maximum number of words in a R/T message
   Max_Words : constant := 31;

   -- Components of a message
   type Word_Index is range 1..Max_Words;
   subtype Word is SystemTypes.Word;
   type Message_Data is array(Word_Index) of Word;
   Null_Message_Data : constant Message_Data :=
     Message_Data'(others => 0);

   -- The message itself
   type Message is record
      Valid : Boolean;
      Fresh : Boolean;
      Data : Message_Data;
   end record;
   Null_Message : constant Message :=
     Message'(Valid => False,
              Fresh => False,
              Data  => Null_Message_Data);

   -- The total number of in or out messages in the system
   type All_Msg_Index is range 0..63;
   --# assert All_Msg_Index'Base is Short_Integer;
   subtype Valid_Msg_Index is All_Msg_Index range
     1..All_Msg_Index'Last;
   -- The max range of Subaddresses for each LRU
   Max_Lru_Subaddress : constant Valid_Msg_Index := 8;
   subtype Lru_Subaddress_Index is Valid_Msg_Index range
     1..Max_Lru_Subaddress;

   -- The LRU entities
   Max_LRUs : constant := 12;
   type LRU_Index is range 1..Max_LRUs;

   -- Write out data to the RT

   -- Make a message valid
   procedure Set_RT_Message_Valid(Subaddress_Idx : in Lru_Subaddress_Index;
                            Dest : in LRU_Index);
   --# global in out Outputs;
   --# derives Outputs from *, Subaddress_Idx, Dest;

   procedure Write_RT_Word(Data    : in Word;
                           Idx     : in Word_Index;
                           Subaddress_Idx : in Lru_Subaddress_Index;
                           Dest    : in LRU_Index);
   --# global in out Outputs;
   --# derives Outputs from *, Data, Idx, Subaddress_Idx, Dest;

   procedure Write_RT_Message(Data    : in Message;
                              Subaddress_Idx : in Lru_Subaddress_Index;
                              Dest    : in LRU_Index);
   --# global in out Outputs;
   --# derives Outputs from *, Data, Subaddress_Idx, Dest;


   -- Write out data to send to the BC destination

   -- Make a message valid
   procedure Set_BC_Message_Valid(Subaddress_Idx : in Lru_Subaddress_Index;
                                  Src : in LRU_Index);
   --# global in out Inputs;
   --# derives Inputs from *, Subaddress_Idx, Src;

   procedure Write_BC_Word(Data    : in Word;
                           Idx     : in Word_Index;
                           Subaddress_Idx : in Lru_Subaddress_Index;
                           Src     : in LRU_Index);
   --# global in out Inputs;
   --# derives Inputs from *, Data, Idx, Subaddress_Idx, Src;

   procedure Write_BC_Message(Data    : in Message;
                              Subaddress_Idx : in Lru_Subaddress_Index;
                              Src     : in LRU_Index);
   --# global in out Inputs;
   --# derives Inputs from *, Data, Subaddress_Idx, Src;


   -- Read data sent to an RT
   function Is_RT_Fresh(Dest : LRU_Index;
                        Subaddress_Idx : in Lru_Subaddress_Index)
                       return Boolean;
   --# global Outputs;

   function Is_RT_Valid(Dest : LRU_Index;
                        Subaddress_Idx : in Lru_Subaddress_Index)
                       return Boolean;
   --# global Outputs;

   procedure Read_RT_Word(Dest    : in LRU_Index;
                          Idx     : in Word_Index;
                          Subaddress_Idx : in Lru_Subaddress_Index;
                          Data    : out Word);
   --# global in Outputs;
   --# derives Data from Dest, Idx, Subaddress_Idx, Outputs;

   procedure Read_RT_Message(Dest    : in LRU_Index;
                             Subaddress_Idx : in Lru_Subaddress_Index;
                             Data    : out Message);
   --# global in Outputs;
   --# derives Data from Dest, Subaddress_Idx, Outputs;

   procedure Acknowledge_RT_Message(Dest : in LRU_Index;
                                    Subaddress_Idx : in Lru_Subaddress_Index);
   --# global in out Outputs;
   --# derives Outputs from *, Dest, Subaddress_Idx;


   -- Read data sent to the BC
   function Is_BC_Fresh(Src : LRU_Index;
                        Subaddress_Idx : in Lru_Subaddress_Index)
                       return Boolean;
   --# global Inputs;

   function Is_BC_Valid(Src : LRU_Index;
                        Subaddress_Idx : in Lru_Subaddress_Index)
                       return Boolean;
   --# global Inputs;

   procedure Read_BC_Word(Src     : in LRU_Index;
                          Idx     : in Word_Index;
                          Subaddress_Idx : in Lru_Subaddress_Index;
                          Data    : out Word);
   --# global in Inputs;
   --# derives Data from Src, Idx, Subaddress_Idx, Inputs;

   procedure Read_BC_Message(Src     : in LRU_Index;
                             Subaddress_Idx : in Lru_Subaddress_Index;
                             Data    : out Message);
   --# global in Inputs;
   --# derives Data from Src, Subaddress_Idx, Inputs;

   procedure Acknowledge_BC_Message(Src : in LRU_Index;
                                    Subaddress_Idx : in Lru_Subaddress_Index);
   --# global in out Inputs;
   --# derives Inputs from *, Src, Subaddress_Idx;


   -- Run a cycle of the bus
   procedure Cycle;
   --# global in out Inputs, Outputs;
   --# derives Inputs, Outputs from *;

   -- Auxiliary debugging routines
   procedure Show_RT(Subaddress_Idx : in Lru_Subaddress_Index;
                     Dest : in LRU_Index);
   --# global in out Outputs;
   --# derives Outputs from *, Subaddress_Idx, Dest;

   procedure Show_BC(Subaddress_Idx : in Lru_Subaddress_Index;
                     Src : in LRU_Index);
   --# global in out Inputs;
   --# derives Inputs from *, Subaddress_Idx, Src;

end Bus;

