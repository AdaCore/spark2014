package body Test_Deep_Volatile with SPARK_Mode is

   procedure Test1 is
      Y : Int_Ptr := X;
   begin
      X := null;
   end Test1;

   procedure Test2 is
      Y : access Integer := X;
   begin
      Y.all := 10;
   end Test2;

   procedure Test3 is
      Y : access constant Integer := X;
   begin
      pragma Assert (Y /= null);
   end Test3;

   procedure Test4 is
      Y : Int_Ptr;
   begin
      Y := X;
      X := null;
   end Test4;

   function Test5 return Int_Ptr is
   begin
      return X;
   end Test5;

   procedure Test6 is
   begin
      P (X);
   end Test6;
end Test_Deep_Volatile;
