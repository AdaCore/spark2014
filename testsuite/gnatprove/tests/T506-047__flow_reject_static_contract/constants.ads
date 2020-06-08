package Constants with SPARK_Mode is

   My_Const : constant Integer := 123_456;

   procedure Proc (X : out Integer) with
     Global => (Input => My_Const);

end Constants;
