package body Type_Invariant_Legal_8 is

   procedure Priv_In (X : T);
   procedure Priv_Out (X : out T);
   procedure Priv_In_Out (X : in out T);

   function Pub (X : T) return Integer is
   begin
      return 1;  --  @INVARIANT_CHECK:NONE
   end Pub;

   function Priv (X : T) return Integer is
   begin
      return 1;  --  @INVARIANT_CHECK:NONE
   end Priv;

   procedure Pub_In (X : T) is
      Tmp : Integer;
   begin
      Tmp := Pub (X);  --  @INVARIANT_CHECK:NONE
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;  --  @INVARIANT_CHECK:NONE
   end Pub_In;

   procedure Priv_In (X : T) is
      Tmp : Integer;
   begin
      Tmp := Pub (X);  --  @INVARIANT_CHECK:NONE
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;  --  @INVARIANT_CHECK:NONE
   end Priv_In;

   procedure Pub_Out (X : out T) is
      Tmp : Integer;
   begin
      X.C := 1;
      Tmp := Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := Priv (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Pub_Out;

   procedure Priv_Out (X : out T) is
      Tmp : Integer;
   begin
      X.C := 1;
      Tmp := Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := Priv (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Priv_Out;

   procedure Pub_In_Out (X : in out T) is
      Tmp : Integer;
   begin
      X.C := X.C - 1;  --  @RANGE_CHECK:PASS
      Tmp := Pub (X);  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv (X);  --  @INVARIANT_CHECK:PASS
      Priv_Out (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Pub_In_Out;

   procedure Priv_In_Out (X : in out T) is
      Tmp : Integer;
   begin
      X.C := X.C - 1;  --  @RANGE_CHECK:FAIL
      Tmp := Pub (X);  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv (X);  --  @INVARIANT_CHECK:PASS
      Pub_Out (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Priv_In_Out;

   procedure Extra_Test (X : in out T) is
   begin
      Pub_In_Out (X);  --  @INVARIANT_CHECK:FAIL
      Priv_In_Out (X);  --  @INVARIANT_CHECK:PASS
      return;  --  @INVARIANT_CHECK:PASS
   end Extra_Test;

end Type_Invariant_Legal_8;
