with Payload;

package Logging
  with SPARK_Mode => On
is

   pragma Warnings (Off, "subprogram ""Log_Payload"" has no effect",
                    Reason => "Not needed for fault reproducer");

   procedure Log_Payload (Data : in Payload.T);

   pragma Warnings (On, "subprogram ""Log_Payload"" has no effect");

end Logging;
