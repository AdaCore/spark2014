package P with Abstract_State => S, SPARK_Mode => On
is
   type T is new Integer range 0 .. 10_000;

   procedure Add (X : in T) with Global => (In_Out => S);
end P;
