package Test_Volatile with SPARK_Mode is
   type Vol is record
      X : Integer;
   end record with Volatile;

   X : Vol with Relaxed_Initialization;

   type I is new Integer with Relaxed_Initialization;

   type R_V is record
      X : I;
   end record with Volatile;

   type A_V is array (1 .. 10) of I with Volatile;

   type R is record
      X : I;
   end record;

   Y : R with Volatile;

   type A is array (1 .. 10) of I;

   Z : A with Volatile;
end Test_Volatile;
