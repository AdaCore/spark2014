private package Externals.Pressure
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers,
                                     Part_Of  => Externals.Combined_Inputs),
       Annotate       => (GNATprove, Always_Return)
is
   procedure Read (Press : out Integer)
     with Global  => State,
          Depends => (Press => State);
end Externals.Pressure;
