procedure Foo with SPARK_Mode is
   type R is null record;
   X : array (1 .. 2) of R := (others => <>);
begin
   null;
end Foo;
