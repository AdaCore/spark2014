package body Trivial_Async_Properties
  with SPARK_Mode
is
   procedure Set is
      U, V : constant Integer := Y;
   begin
      pragma Assert (U = V);

      X := 0;
      X := 1;
   end Set;

end Trivial_Async_Properties;
