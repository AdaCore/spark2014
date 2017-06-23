package body Ident
  with SPARK_Mode
is

   function Id_Body (X : Integer) return Integer;
   procedure Incr_Body (X : in Positive; Y : out Natural);

   function Id_Body (X : Integer) return Integer is
   begin
      return X;
   end Id_Body;

   procedure Incr_Body (X : in Positive; Y : out Natural) is
   begin
      Y := X - 1;
   end Incr_Body;

   function Id_Public (X : Integer) return Integer is
   begin
      return X;
   end Id_Public;

   procedure Incr_Public (X : in Positive; Y : out Natural) is
   begin
      Y := X - 1;
   end Incr_Public;

   function Id_Private (X : Integer) return Integer is
   begin
      return X;
   end Id_Private;

   procedure Incr_Private (X : in Positive; Y : out Natural) is
   begin
      Y := X - 1;
   end Incr_Private;

   procedure Test is
      X : Integer := 10;
      Y : Integer;
      Res : Integer;
   begin
      Res := Id_Public (X);
      pragma Assert (Res = X);     -- @ASSERT:FAIL
      Res := Id_Private (X);
      pragma Assert (Res = X);     -- @ASSERT:FAIL
      Res := Id_Body (X);
      pragma Assert (Res = X);     -- @ASSERT:PASS

      Incr_Public (X, Y);
      pragma Assert (Y = 9);   -- @ASSERT:FAIL
      Incr_Private (X, Y);
      pragma Assert (Y = 9);   -- @ASSERT:FAIL
      Incr_Body (X, Y);
      pragma Assert (Y = 9);   -- @ASSERT:PASS
   end Test;

end Ident;
