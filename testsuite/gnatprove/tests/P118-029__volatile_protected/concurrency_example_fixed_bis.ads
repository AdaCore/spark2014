package Concurrency_Example_Fixed_Bis is

   Ext_Data : Integer := 0 with
     Volatile,
     Part_Of => Data;

   protected Data is
      function Get return Integer;
      procedure Set (V : Integer);
   private
   end Data;

   task Writer;
   task Reader;

end Concurrency_Example_Fixed_Bis;
