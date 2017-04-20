procedure Overflow_Modulus with SPARK_Mode is
   type T is mod 2 ** 8;
   function ID (X : Natural) return Natural is (X);
   Max : constant := 2 ** 8 + 1;
   type T2 is mod 2 ** 3;

   X : T;
   Y : T2;
begin
   X := 2 ** ID (Max);
   pragma Assert (X = 0);
   Y := 2 ** ID (3);
   pragma Assert (Y = 0);
end Overflow_Modulus;
