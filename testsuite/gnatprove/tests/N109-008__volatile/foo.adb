package body Foo with SPARK_Mode is
   type T is new Integer with Volatile;

   procedure P (X : in T; Y : out Integer)
     with Post => Integer (X) = Y
   is
   begin
      Y := Integer (X);
   end P;
end Foo;
