package Parent with
  SPARK_Mode
is
   type T is tagged null record;
   procedure P (X : T) with Pre'Class => True;
   procedure Q (X : T);
end Parent;
