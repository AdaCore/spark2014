package Dispatch with SPARK_Mode is
   type Root is tagged record
      F : Integer;
   end record;

   function Init return Root is (F => 0);

   package Nested is
      type Child is new Root with record
         G : Integer;
      end record;

      function Init return Child is (F => 1, G => 1);
   end Nested;
end Dispatch;
