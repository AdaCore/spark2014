procedure Main with SPARK_Mode is

   procedure P with
     Import,
     Annotate => (GNATprove, Terminating);

begin
   P;
end Main;
