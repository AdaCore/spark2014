package body Test with
  SPARK_Mode
is

   function Test return Boolean is
      function X return Natural is (14);
   begin
      return Long_Integer'(2**X) <= Long_Integer'Last;
   end Test;

end Test;
