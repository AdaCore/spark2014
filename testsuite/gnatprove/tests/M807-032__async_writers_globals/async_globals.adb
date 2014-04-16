package body Async_Globals is

   G : Integer with Volatile, Async_Writers;

   procedure Get_1 (X : out Integer) is
   begin
      X := G;
   end Get_1;

   procedure Get_2 (X : out Integer)
   with Global => G
   is
   begin
      X := G;
   end Get_2;

   procedure Test_1 (X : out Integer;
                     Y : out Integer)
   with Pre => True
   is
   begin
      Get_1 (X);
      Get_1 (Y);
      pragma Assert (X = Y);  --  should not be provable
   end Test_1;

   procedure Test_2 (X : out Integer;
                     Y : out Integer)
   with Pre => True
   is
   begin
      Get_2 (X);
      Get_2 (Y);
      pragma Assert (X = Y);  --  should not be provable
   end Test_2;

end Async_Globals;
