package Read_Write with
  SPARK_Mode
is

   V : Boolean;

   procedure P with
     Global => (In_Out => V),
     Pre    => not V,
     Post   => V;

end Read_Write;
