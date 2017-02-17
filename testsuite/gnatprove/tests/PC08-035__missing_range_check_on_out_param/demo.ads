package Demo
with SPARK_Mode => On is

   subtype range_A is Float range 10.0 .. 20.0;
   subtype range_B is Float range -20.0 .. -10.0;

   procedure caller (b : out range_B);

end Demo;
