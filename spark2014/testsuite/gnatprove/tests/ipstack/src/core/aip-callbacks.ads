------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Callbacks is

   --  Since we can't use access to subprograms in SPARK, callbacks are
   --  identified by IPTR values and the applicative data argument as well.

   subtype Callback_Id is AIP.IPTR_T;
   NOCB : constant Callback_Id := AIP.NULIPTR;

   --  The general scheme is as follows (PROTO = UDP|TCP):
   --
   --  App calls  PROTO_Callback (Evkind, PCB, Cbid);  to mean
   --
   --  "When a event of kind Evkind triggers for PCB, call the PROTO_Event
   --  handler with an event descriptor and pass back Cbid".
   --
   --  PROTO_Event (Ev; PCB; Cbid) is to be defined by the applicative layer.
   --  Ev is to be typed as PROTO_Event_T, the contents of which varies
   --  with the protocol.

end AIP.Callbacks;
