package Bad with
  SPARK_Mode,
  Elaborate_Body
is

   type I1 is interface;
   function F (Obj : I1) return Integer is abstract;

   type I2 is interface;
   function F (Obj : I2) return Integer is abstract with
     Post'Class => F'Result >= 0;

   type T3 is new I1 and I2 with null record;
   overriding function F (Obj : T3) return Integer is (10);

end Bad;
