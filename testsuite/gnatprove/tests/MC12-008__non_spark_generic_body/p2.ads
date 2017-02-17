package P2
  with SPARK_Mode => On
is
   type T is range 1 .. 10;

   procedure Do_It1 (X : in out T)
     with Pre => X < T'Last;

end P2;
