package body Async_Globals is

   G : Integer with Volatile, Async_Writers;

   procedure Get (X : out Integer) is
   begin
      X := G;
   end Get;

   procedure Test (X : out Integer;
                   Y : out Integer)
   is
   begin
      Get (X);
      Get (Y);
      pragma Assert (X = Y);  --  should not be provable
   end Test;

end Async_Globals;
