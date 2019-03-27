procedure Spark01
  with SPARK_Mode
is
   package Data is
      type MyStruct is record
         A,B : Integer;
      end record;
      function GetA (X : MyStruct) return Integer with
        Pre => X.A >= 0,
        Post => GetA'Result = X.A;

   end Data;

   package body Data
   is
      function GetA (X : MyStruct) return Integer is (X.A);
   end Data;

   use Data;

   X : MyStruct := MyStruct'(A => 10, B => 12);
   Z : Integer := 0;
begin
   X := MyStruct'(A => 42, B => 43);
end Spark01;
