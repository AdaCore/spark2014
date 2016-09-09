package body Type_Invariant_Legal with SPARK_Mode is

   procedure Priv_In (X : T) with Pre => True;  --  @INVARIANT_CHECK:NONE
   procedure Priv_Out (X : out T) with Pre => True;  --  @INVARIANT_CHECK:NONE
   procedure Priv_In_Out (X : in out T) with Pre => True;  --  @INVARIANT_CHECK:NONE

   function Pub return T is
   begin
      return 0;
   end Pub;

   function Priv return T is
   begin
      return 0;
   end Priv;

   procedure Pub_In (X : T) is
   begin
      return;
   end Pub_In;

   procedure Priv_In (X : T) is
   begin
      return;
   end Priv_In;

   procedure Pub_Out (X : out T) is
   begin
      X := 1;
      return;
   end Pub_Out;

   procedure Priv_Out (X : out T) is
   begin
      X := 1;
      return;
   end Priv_Out;

   procedure Pub_In_Out (X : in out T) is
   begin
      X := X - 1;  --  @RANGE_CHECK:PASS
      return;
   end Pub_In_Out;

   procedure Priv_In_Out (X : in out T) is
   begin
      X := X - 1;  --  @RANGE_CHECK:FAIL
      return;
   end Priv_In_Out;

end Type_Invariant_Legal;
