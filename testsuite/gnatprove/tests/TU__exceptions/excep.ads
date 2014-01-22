package Excep
  with SPARK_Mode => On
is

   Oops : exception;

   procedure Bad1 (X : in out Integer);

   procedure Bad2 (X : in out Integer);

   procedure Bad3 (X : in out Integer);

   procedure Bad4 (X : in out Integer);

   procedure OK1 (X : in out Integer);

   procedure OK2 (X : in out Integer);
end Excep;
