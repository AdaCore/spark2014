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

with Process_DNS_Request,
     Task_Limit;

package body Multitask_Process_DNS_Request
  with SPARK_Mode => Off
is
   Task_Limit_Object : Task_Limit.Task_Count_Type;
   task type Handle_TCP_Request
     with Global  => (In_Out => (DNS_Network.Network,
                                 Protected_SPARK_IO_05.SPARK_IO_PO)),
          Depends => ((DNS_Network.Network,
                       Protected_SPARK_IO_05.SPARK_IO_PO) =>+
                         DNS_Network.Network)
   is
      entry Start (Reply_Socket : in DNS_Network.DNS_Socket);
      pragma Priority (0);
   end Handle_TCP_Request;

   type Task_Ptr is access all Handle_TCP_Request;

   task body Handle_TCP_Request is
      The_Socket : DNS_Network.DNS_Socket;
   begin
      accept Start (Reply_Socket : in DNS_Network.DNS_Socket) do
         The_Socket := Reply_Socket;
      end Start;

      Process_DNS_Request.Process_Request_TCP (Reply_Socket => The_Socket);
      Task_Limit_Object.Decrement;
   end Handle_TCP_Request;

   procedure Process_Request_TCP (Reply_Socket : in DNS_Network.DNS_Socket) is
      T       : Task_Ptr;
      Success : Boolean;
   begin
      Task_Limit_Object.Increment (Success);
      if Success then
         T := new Handle_TCP_Request;
         T.Start (Reply_Socket);
      else
         DNS_Network.Discard_Socket (Reply_Socket);
      end if;
      --Process_DNS_Request.Process_Request_TCP (Reply_Socket => Reply_Socket);
   end Process_Request_TCP;

end Multitask_Process_DNS_Request;
