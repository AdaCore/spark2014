package body Type_Invariant_Legal_5 with
  Refined_State => (State => X)
is

   procedure Priv_In with Global => (Input => X);
   procedure Priv_Out with Global => (Output => X);
   procedure Priv_In_Out with Global => (In_Out => X);

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
      Tmp := Pub;  --  @INVARIANT_CHECK:NONE
      Tmp := Priv;  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub;  --  @INVARIANT_CHECK:NONE
      Tmp := E_Priv;  --  @INVARIANT_CHECK:NONE
      return;  --  @INVARIANT_CHECK:NONE
   end Pub_In;

   procedure Priv_In is
      Tmp : Integer;
   begin
      Tmp := Pub;  --  @INVARIANT_CHECK:NONE
      Tmp := Priv;  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub;  --  @INVARIANT_CHECK:NONE
      Tmp := E_Priv;  --  @INVARIANT_CHECK:NONE
      return;  --  @INVARIANT_CHECK:NONE
   end Priv_In;

   procedure Pub_Out is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Pub_Out;

   procedure Priv_Out is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := Priv;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub;  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv;  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:NONE
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
      return;  --  @INVARIANT_CHECK:PASS
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
      return;  --  @INVARIANT_CHECK:PASS
   end Priv_In_Out;

   procedure Extra_Test with
     Global => (In_Out => X)
   is
   begin
      Pub_In_Out;  --  @INVARIANT_CHECK:PASS
      Priv_In_Out;  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Extra_Test;

end Type_Invariant_Legal_5;
