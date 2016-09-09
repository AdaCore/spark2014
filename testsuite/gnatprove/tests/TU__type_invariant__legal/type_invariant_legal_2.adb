package body Type_Invariant_Legal_2 with SPARK_Mode is

   procedure Priv_In (X : T) with Pre => True;  --  @INVARIANT_CHECK:NONE
   procedure Priv_Out (X : out T) with Pre => True;  --  @INVARIANT_CHECK:NONE
   procedure Priv_In_Out (X : in out T) with Pre => True;  --  @INVARIANT_CHECK:NONE

   function Pub (X : T) return Integer is
   begin
      return 1;
   end Pub;

   function Priv (X : T) return Integer is
   begin
      return 1;
   end Priv;

   procedure Pub_In (X : T) is
      Tmp : Integer;
   begin
      Tmp := Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Pub_In;

   procedure Priv_In (X : T) is
      Tmp : Integer;
   begin
      Tmp := Pub (X);  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Priv_In;

   procedure Pub_Out (X : out T) is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Pub_Out;

   procedure Priv_Out (X : out T) is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Priv_Out;

   procedure Pub_In_Out (X : in out T) is
      Tmp : Integer;
   begin
      X := X - 1;  --  @RANGE_CHECK:PASS
      Tmp := Pub (X);  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Priv_Out (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:FAIL
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Pub_In_Out;

   procedure Priv_In_Out (X : in out T) is
      Tmp : Integer;
   begin
      X := X - 1;  --  @RANGE_CHECK:FAIL
      Tmp := Pub (X);  --  @INVARIANT_CHECK:FAIL
      Tmp := Priv (X);  --  @INVARIANT_CHECK:NONE
      Pub_Out (X);  --  @INVARIANT_CHECK:NONE
      Tmp := E_Pub (X);  --  @INVARIANT_CHECK:PASS
      Tmp := E_Priv (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Priv_In_Out;

   procedure Extra_Test (X : in out T) is  --  @INVARIANT_CHECK:NONE
   begin
      Pub_In_Out (X);  --  @INVARIANT_CHECK:FAIL
      Priv_In_Out (X);  --  @INVARIANT_CHECK:NONE
      return;
   end Extra_Test;

end Type_Invariant_Legal_2;
