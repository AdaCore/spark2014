with Connection; use Connection;

package Use_Connection
  with SPARK_Mode
is
   type IO_Pulse_T is record
      Coid : Connection_Id_T;
   end record with Relaxed_Initialization;
end;
