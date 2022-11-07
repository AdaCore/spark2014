with Connection; use Connection;

package Use_Connection
  with SPARK_Mode
is
   type IO_Pulse_T is record
      Coid : Connection_Id_T;
   end record with Relaxed_Initialization;

   procedure Init_Null (Pulse : in out IO_Pulse_T)
   with
     Post => Pulse.Coid'Initialized and then Pulse.Coid = Null_Connection,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   procedure Init (Pulse : in out IO_Pulse_T)
   with
     Global => null,
     Annotate => (GNATprove, Always_Return);
end;
