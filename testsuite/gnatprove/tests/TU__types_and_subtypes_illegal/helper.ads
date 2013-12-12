package Helper
  with SPARK_Mode => Off
is
   type Integer_Access is access Integer;

   function Return_Some_Access return Integer_Access is (null);
end Helper;
