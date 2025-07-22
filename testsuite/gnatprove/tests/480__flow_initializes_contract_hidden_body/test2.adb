package body Test2
with
   SPARK_Mode => Off,
   Refined_State => (State => Count)
is

   Count : Natural := External.Get_State;

   procedure Update is null;

end Test2;
