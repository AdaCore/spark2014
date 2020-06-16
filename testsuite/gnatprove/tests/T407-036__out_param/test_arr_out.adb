procedure Test_Arr_Out with SPARK_Mode
is
   function Id (X : Positive) return Positive is (X);

   X : constant Positive := Id (1);
   Y : constant Positive := Id (2);

   type Arr_Ty is array (Positive range <>) of Natural;
   subtype S1 is Arr_Ty (X .. X + 10);
   subtype S2 is Arr_Ty (Y .. Y + 10);

   procedure Update_One (C : in out S1) with
     Post => C (X + 3) = 0
   is
   begin
      C (X + 3) := 0;
   end Update_One;

   V : S2 := (others => 1);
begin
   Update_One (V);
   pragma Assert (V (Y + 2) = 0); --@ASSERT:FAIL
end;
