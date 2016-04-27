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

with DNS_Network,
     DNS_Table_Pkg,
     Multitask_Process_DNS_Request,
     Protected_SPARK_IO_05,
     Ada.Synchronous_Task_Control;

package TCP_DNS_Package
  with Abstract_State => (Startup_Suspension with External)
is
   procedure Initialization_Done
   with Global  => (Output => Startup_Suspension),
        Depends => (Startup_Suspension => null);

   task type TCP_DNS_Task
     with Global  => (Output => Startup_Suspension,
                      In_Out => (DNS_Table_Pkg.DNS_Table,
                                 DNS_Network.Network,
                                 Protected_SPARK_IO_05.SPARK_IO_PO)),
          Depends => ((DNS_Network.Network,
                       Protected_SPARK_IO_05.SPARK_IO_PO) =>+
                         (DNS_Network.Network,
                          DNS_Table_Pkg.DNS_Table),
                      DNS_Table_Pkg.DNS_Table =>+ null,
                      Startup_Suspension => null)
   is
      pragma Priority(0);
   end TCP_DNS_Task;

end TCP_DNS_Package;
