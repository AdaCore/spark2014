package Pack is pragma SPARK_Mode (On);

   X : Boolean;

   procedure P0 with SPARK_Mode => On, Post => X = True;
   procedure P1 with SPARK_Mode => On, Post => X = True;
   procedure P2 with SPARK_Mode => On, Post => X = True;
   procedure P3 with SPARK_Mode => Off, Post => X = True;
   procedure P4 with SPARK_Mode => On, Post => X = True;
   procedure P5 with SPARK_Mode => On, Post => X = True;

end;
