package Volatile_Access with SPARK_Mode Is
   X : aliased Integer := 15 with Volatile;

   procedure P;
end Volatile_Access;
