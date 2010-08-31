------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;
with AIP.TCP;
with AIP.PCBs;
with AIP.Callbacks;

package RAW_TCP_Callbacks is

   type TCP_Hook is
     access procedure (Ev  : AIP.TCP.TCP_Event_T;
                       Pcb : AIP.PCBs.PCB_Id;
                       Err : out AIP.Err_T);

   function To_CBID is new
     Ada.Unchecked_Conversion (TCP_Hook, AIP.Callbacks.CBK_Id);

   function To_Hook is new
     Ada.Unchecked_Conversion (AIP.Callbacks.CBK_Id, TCP_Hook);

end RAW_TCP_Callbacks;
