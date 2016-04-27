----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

package body TCP_DNS_Package
  with Refined_State => (Startup_Suspension => (The_Task,
                                                The_Startup_Suspension))
is
   The_Task : TCP_DNS_Task;
   The_Startup_Suspension : Ada.Synchronous_Task_Control.Suspension_Object;

   procedure Initialization_Done is
   begin
      Ada.Synchronous_Task_Control.Set_True (The_Startup_Suspension);
   end Initialization_Done;

   ------------------
   -- TCP_DNS_Task --
   ------------------

   task body TCP_DNS_Task is
      Reply_Socket : DNS_Network.DNS_Socket;
   begin
      Ada.Synchronous_Task_Control.Suspend_Until_True (The_Startup_Suspension);
      -- start listening on a port
      DNS_Network.Initialize_TCP;
      loop
         -- get a connection
         DNS_Network.Get_Connection_TCP (Socket => Reply_Socket);
         -- process the request and reply
         Multitask_Process_DNS_Request.Process_Request_TCP
           (Reply_Socket => Reply_Socket);
      end loop;
   end TCP_DNS_Task;

end TCP_DNS_Package;
