private package Externals.Temperature
  with SPARK_Mode,
       Abstract_State => (State with External => Async_Writers,
                                     Part_Of  => Externals.Combined_Inputs),
       Annotate       => (GNATprove, Always_Return)
is
   procedure Read (Temp : out Integer)
     with Global  => State,
          Depends => (Temp => State);
end Externals.Temperature;
