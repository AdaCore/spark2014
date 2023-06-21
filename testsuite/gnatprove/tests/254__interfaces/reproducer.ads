package Reproducer with
  SPARK_Mode,
  Elaborate_Body
is

   type I1 is interface;
   function F (Obj : I1) return Integer is abstract;

   type I2 is interface and I1;
   overriding function F (Obj : I2) return Integer is abstract with
     Post'Class => F'Result >= 0;

   type T3 is new I2 with null record;
   overriding function F (Obj : T3) return Integer is (10);

end Reproducer;
