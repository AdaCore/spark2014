package A.B with
  SPARK_Mode
is
   procedure example with
     Global => (In_Out => aDATA1), Depends => (aDATA1 => aDATA1);
end A.B;
