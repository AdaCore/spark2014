-- IBIT state machine
--
-- $Log: ibit.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/10 20:05:38  adi
-- Fixed state for BIT changes
--
-- Revision 1.2  2003/02/11 20:48:43  adi
-- Added the RT state machine
--
-- Revision 1.1  2003/02/11 20:35:15  adi
-- Initial revision
--
--
package body IBIT is
   -- The standard IBIT state machine for the MCU,
   -- reading Bus_Data off the bus from the relevant RT
   -- and changing its internal Phase variable accordingly.

   procedure State_Machine(Bus_Data : in SystemTypes.Unsigned16;
                           Current_Phase : in out Phase)
   is
   begin
      case Current_Phase is
         when Off =>
            null;
         when Request_Start =>
            -- Expect to see In_Progress eventually
            if Bus_Data = Phase_Lookup(In_Progress) then
               Current_Phase := In_Progress;
            end if;
         when In_Progress =>
            -- Expect to see pass or fail
            if Bus_Data = Phase_Lookup(Pass) then
               Current_Phase := Pass;
            elsif Bus_Data = Phase_Lookup(Fail) then
               Current_Phase := Fail;
            else
               null;
            end if;
         when Request_Stop =>
            -- Expect to see Off eventually
            if Bus_Data = Phase_Lookup(Off) then
               Current_Phase := Off;
            end if;
         when Pass | Fail | Timeout =>
            -- skip
            null;
      end case;
   end State_Machine;


   -- The standard IBIT state machine for RTs,
   -- reading Bus_Data off the bus from the MCU
   -- and changing its internal Phase variable accordingly.

   procedure RT_State_Machine(Bus_Data : in SystemTypes.Unsigned16;
                           Current_Phase : in out Phase)
   is
   begin
      case Current_Phase is
         when Off | Pass | Fail =>
            -- Expect to see request_start eventually
            if Bus_Data = Phase_Lookup(Request_Start) then
               Current_Phase := In_Progress;
            end if;
         when Request_Start | Request_Stop | Timeout =>
            -- Shouldn't happen
            null;
         when In_Progress =>
            -- Expect to see a request_stop
            if Bus_Data = Phase_Lookup(Request_Stop) then
               Current_Phase := Off;
            end if;
      end case;
   end RT_State_Machine;

end IBIT;

