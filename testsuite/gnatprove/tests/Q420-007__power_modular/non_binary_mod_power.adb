procedure Non_Binary_Mod_Power with SPARK_Mode is
   type T1 is mod 2 ** 8;
   type T2 is mod 5;

   function ID (X : T1) return T1 is (X);
   function ID (Y : T2) return T2 is (Y);
   function ID (Z : Integer) return Integer is (Z);

   X : T1 := ID (2);
   Y : T2 := ID (2);
   Z : Integer := ID (2);
begin
   X := X ** 4;
   Y := Y ** 4;
   Z := (Z ** 4) mod 5;
   pragma Assert (Z = Integer (Y));
   pragma Assert (X = T1 (Y)); --@ASSERT:FAIL
end Non_Binary_Mod_Power;
