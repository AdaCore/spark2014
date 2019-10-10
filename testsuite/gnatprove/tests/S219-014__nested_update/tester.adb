pragma Spark_Mode (On);

with Ada.Text_Io;
with Generic_Ring_Buffer;


procedure Tester
is

   package Ring_Buffer is new Generic_Ring_Buffer
     (Element_Type => Integer);
   use Ring_Buffer;


   X : Ring_Buffer_Type (4);
   Element : Integer;
   Counter : Integer;
begin
--   X.Items := (others => 0);
   Put (X, 1);
   Get (X, Element);
   Put (X, 2);
   Put (X, 3);
   Put (X, 4);
   Put (X, 5);

   Counter := Size (X); -- defined in Generic_Ring_Buffer
   for I in Natural range 1 .. Counter loop
      Get (X, Element);
      Ada.Text_Io.Put_Line (Integer'Image (Element));
   end loop;

end Tester;
