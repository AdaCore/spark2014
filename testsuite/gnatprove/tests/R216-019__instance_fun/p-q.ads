package P.Q
with
  SPARK_Mode     => On,
  Abstract_State => Hash,
  Initializes    => Hash
is

   procedure Foo (ID : out Integer)
   with Global => (In_Out => Hash);

end P.Q;
