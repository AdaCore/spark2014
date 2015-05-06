------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Definition of external (application-level) callbacks

package AIP.Callbacks is

   pragma Pure;

   --  Since we can't use access to subprograms in SPARK, callbacks are
   --  identified by arbitrary opaque identifiers. We arrange for these to be
   --  the same size as a machine address, still, to let users assign
   --  subprogram access values (with user level intermediate conversions) if
   --  they like.

   type CBK_Id is mod 2 ** AIP_Constants.Address_Size;
   NOCB : constant CBK_Id := 0;

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
