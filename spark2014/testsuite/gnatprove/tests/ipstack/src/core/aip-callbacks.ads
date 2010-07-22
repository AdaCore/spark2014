------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Definition of external (application-level) callbacks

--# inherit AIP;

package AIP.Callbacks is

   pragma Pure;

   --  Since we can't use access to subprograms in SPARK, callbacks and the
   --  associated application level data are identified by arbitrary opaque
   --  identifiers.

   subtype CBK_Id is AIP.EID;
   NOCB : constant CBK_Id := AIP.NULID;

   --  The general scheme is as follows (PROTO = UDP|TCP):
   --
   --  Application calls:
   --    <PROTO>_Callback (Evkind, PCB, Cbid);
   --  to request that whenever an event with kind EvKind is triggered for
   --  PCB, the <PROTO>_Event handler be called with an event descriptor
   --  including Cbid as the callback identifier.
   --
   --  <PROTO>_Event (Ev, PCB, Cbid) is to be defined by the application.
   --  Ev is to be typed as <PROTO>_Event_T, the contents of which varies
   --  with the protocol.

end AIP.Callbacks;
