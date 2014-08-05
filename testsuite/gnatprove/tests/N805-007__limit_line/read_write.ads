package Read_Write with
  SPARK_Mode
is

   V : Boolean;

   procedure Q with
     Global => (In_Out => V);

   procedure P with
     Pre    => not V,
     Post   => V;

end Read_Write;
