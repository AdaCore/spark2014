package SPARK_IO
  with Abstract_State => State,
       Initializes    => State
is

   procedure Put_Line (S : in String)
      with Global => (In_Out => State);

end SPARK_IO;
