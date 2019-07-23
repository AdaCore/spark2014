pragma Spark_Mode (On);

with Generic_Ring_Buffer;


procedure Tester
is

   package Ring_Buffer is new Generic_Ring_Buffer
     (Element_Type => Integer);
   use Ring_Buffer;

   X : Ring_Buffer_Type (4);

begin
   Put (X, 1);
end Tester;
