package LT
  with SPARK_Mode => On
is
   subtype Bit is Integer range 0 .. 1;
   subtype N is Integer range 0 .. 9;

   subtype Sum is Integer range 0 .. 100;

   type Row is array (N) of Bit;
   type Table is array (N) of Row;

   function Total (X : in Table) return Sum;

end LT;
