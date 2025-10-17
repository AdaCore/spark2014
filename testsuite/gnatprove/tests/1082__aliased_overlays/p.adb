procedure P with SPARK_Mode is
   type R2 is record
      X, Y : Character;
   end record;

   procedure Test_Object_Size_Aliased is
      Z : R2 := ('a', 'b') with Size => 16;
      X : aliased R2
      with Import, Address => Z'Address, Size => 24;  --  Should be rejected, X and Z do not have the same size
   begin
      null;
   end Test_Object_Size_Aliased;
begin
   null;
end P;
