package Remote
  with SPARK_Mode,
       Abstract_State => State
is
   Var : Integer;

   procedure Init_State
     with Global   => (Output => State),
          Annotate => (GNATprove, Always_Return);
end Remote;
