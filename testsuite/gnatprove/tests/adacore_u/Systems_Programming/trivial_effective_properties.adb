package body Trivial_Effective_Properties
  with SPARK_Mode
is
   procedure Set is
   begin
      X := Y;
      X := 0;
   end Set;

end Trivial_Effective_Properties;
