package P with SPARK_Mode is

   protected PO is
      function Get return Integer;
   end;

private
   pragma SPARK_Mode (Off);

   Ptr : access Integer := null with Part_Of => PO;
end;
