package Atom3 with SPARK_Mode is

   Data : Integer with Atomic, Async_Readers => True, Async_Writers => True;

   function Get_Data return Integer is (Data) with Volatile_Function;

   function Get_Data_Plus_One return Integer is (Data + 1) with Volatile_Function;

end Atom3;
