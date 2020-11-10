package body P is
   protected body Outer_Type is
      function Outer_Fun (Inner_data : Integer) return Integer is
         type T is new Integer range Inner_data .. Outer_Data;
      begin
         return 0;
      end Outer_Fun;
   end Outer_Type;
end P;
