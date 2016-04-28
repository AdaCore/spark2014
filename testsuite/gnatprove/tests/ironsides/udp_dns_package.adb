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

with Protected_SPARK_IO_05;

package body UDP_DNS_Package
  with SPARK_Mode => Off,
       Refined_State => (Startup_Suspension => (The_Startup_Suspension,
                                                The_Task))
is
   --type Task_Array is array (1 .. 10) of UDP_DNS_Task;
   The_Task : UDP_DNS_Task;
   --the_tasks : task_array;
   The_Startup_Suspension : Ada.Synchronous_Task_Control.Suspension_Object;

   procedure Initialization_Done is
   begin
      Ada.Synchronous_Task_Control.Set_True (The_Startup_Suspension);
   end Initialization_Done;

   ------------------
   -- UDP_DNS_Task --
   ------------------

   task body UDP_DNS_Task is
      Input_Packet  : DNS_Types.DNS_Packet;
      Input_Bytes   : DNS_Types.Packet_Length_Range;
      Reply_Address : DNS_Network.Network_Address_And_Port;
      Output_Packet : DNS_Types.DNS_Packet;
      Output_Bytes  : DNS_Types.Packet_Length_Range;
      Failure       : Boolean;
      Max_Transmit  : DNS_Types.Packet_Length_Range;
   begin
      DNS_Network.Initialize_UDP;
      Ada.Synchronous_Task_Control.Suspend_Until_True (The_Startup_Suspension);
      Output_Packet.Bytes := DNS_Types.Bytes_Array_Type'(others => 0);
      Output_Packet.Header := DNS_Types.Empty_Header;
      loop
         DNS_Network_Receive.Receive_DNS_Packet
           (Packet        => Input_Packet,
            Number_Bytes  => Input_Bytes,
            Reply_Address => Reply_Address,
            Failure       => Failure);
         if Failure then
            Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
              (Protected_SPARK_IO_05.Standard_Output,
               "Receive failed",
               0);
         else
            Process_DNS_Request.Create_Response
              (Input_Packet  => Input_Packet,
               Input_Bytes   => Input_Bytes,
               Output_Packet => Output_Packet,
               Output_Bytes  => Output_Bytes,
               Max_Transmit  => Max_Transmit);
            -- since there is a restriction on UDP messages, cap the UDP size
            -- here

            -- Max_Transmit will be higher if EDNS0
            Output_Bytes := DNS_Types.Packet_Length_Range'Min (Max_Transmit,
                                                               Output_Bytes);

            DNS_Network.Send_DNS_Packet
              (Packet       => Output_Packet,
               Number_Bytes => Output_Bytes,
               To_Address   => Reply_Address,
               Failure      => Failure);

            if Failure then
               Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
                 (Protected_SPARK_IO_05.Standard_Output,
                  "send failed",
                  0);
            end if;
         end if;
      end loop;
   end UDP_DNS_Task;

end UDP_DNS_Package;
