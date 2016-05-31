package Parent
   with SPARK_Mode => On
is
   subtype T is Integer range 5 .. 99;

   procedure P (X : in out T);

end Parent;
