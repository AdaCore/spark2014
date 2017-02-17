package P
  with SPARK_Mode => On
is
   procedure Op1 (X : in out Integer);

   procedure Op2 (X : in out Integer);

   function F1 (X : in Integer) return Integer;

   function F2 (X : in Integer) return Integer;

end P;
