-- IBIT types
--
-- $Log: ibit.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/02/11 20:48:34  adi
-- Added the RT state machine
--
-- Revision 1.2  2003/02/11 20:31:32  adi
-- Added State_Machine
--
-- Revision 1.1  2003/02/11 19:39:03  adi
-- Initial revision
--
--
with SystemTypes;
--# inherit SystemTypes;
package IBIT is

   type Phase is (Off,Request_Start,In_Progress,
                  Request_Stop,Pass,Fail,Timeout);

   type Phase_Table is array(Phase) of SystemTypes.Byte;
   Phase_Lookup : constant Phase_Table
     := Phase_Table'(Off => 1,
                     Request_Start => 2,
                     In_Progress => 2,
                     Request_Stop => 1,
                     Pass => 4,
                     Fail => 8,
                     Timeout => 16);

   -- Phase state machine for the MCU, reading data from the RTs
   procedure State_Machine(Bus_Data : in SystemTypes.Unsigned16;
                           Current_Phase : in out Phase);
   --# derives Current_Phase from *, Bus_Data;

   -- Phase state machine for the RTs, reading data from the MCU
   procedure RT_State_Machine(Bus_Data : in SystemTypes.Unsigned16;
                              Current_Phase : in out Phase);
   --# derives Current_Phase from *, Bus_Data;

end IBIT;

