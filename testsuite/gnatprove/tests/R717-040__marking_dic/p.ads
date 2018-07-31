package P with SPARK_Mode, Abstract_State => S is
   procedure Flip with Global => (In_Out => S);
end;
