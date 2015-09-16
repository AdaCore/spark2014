package body Volfun
  with SPARK_Mode
is
   function H return Integer is
   begin
      return F + 1;
   end H;
end Volfun;
