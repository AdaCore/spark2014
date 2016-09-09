package body Type_Invariant_Legal_4 with SPARK_Mode,
  Refined_State => (State => X)
is

   procedure Priv_In with Pre => True;  --  @INVARIANT_CHECK:NONE
   procedure Priv_Out with Pre => True, Global => (Output => X);  --  @INVARIANT_CHECK:PASS
   procedure Priv_In_Out with Pre => True;  --  @INVARIANT_CHECK:PASS

   function Pub return Integer is
   begin
      return Integer(X);  --  @INVARIANT_CHECK:NONE
   end Pub;

   function Priv return Integer is
   begin
      return Integer(X);  --  @INVARIANT_CHECK:NONE
   end Priv;

   procedure Pub_In is
      Tmp : Integer;
   begin
      Tmp := Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;
   end Pub_In;

   procedure Priv_In is
      Tmp : Integer;
   begin
      Tmp := Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;
   end Priv_In;

   procedure Pub_Out with Refined_Global => (Output => X) is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;
   end Pub_Out;

   procedure Priv_Out is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;
   end Priv_Out;

   procedure Pub_In_Out is
      Tmp : Integer;
   begin
      X := X - 1;  --  @RANGE_CHECK:PASS
      Tmp := Pub;  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Priv_Out;  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;
   end Pub_In_Out;

   procedure Priv_In_Out is
      Tmp : Integer;
   begin
      X := X - 1;  --  @RANGE_CHECK:PASS
      Tmp := Pub;  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Pub_Out;  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;
   end Priv_In_Out;

   procedure Extra_Test is  --  @INVARIANT_CHECK:PASS
   begin
      Pub_In_Out;  --  @INVARIANT_CHECK:PASS
      Priv_In_Out;  --  @INVARIANT_CHECK:PASS
      return;
   end Extra_Test;

end Type_Invariant_Legal_4;
