package body P with SPARK_Mode => Off is

   function Expose return Integer is (Secret);

end;
