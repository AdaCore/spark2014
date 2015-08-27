package Test
   with SPARK_Mode
is
   procedure P (X : in integer;
    Y : out integer)
    with SPARK_Mode,
    Pre => (X in 1..2);
end Test;
