package Atom with SPARK_Mode is

   Data : Integer with Atomic;

   function Get_Data return Integer is (Data);

   function Get_Data_Plus_One return Integer is (Data + 1);

end Atom;
