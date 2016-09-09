with External_6; use External_6;

package body Type_Invariant_Legal_6 with SPARK_Mode is

   function Priv (X : T) return Integer with Pre => True;
   procedure Priv_In (X : T) with Pre => True;
   procedure Priv_Out (X : out T) with Pre => True;
   procedure Priv_In_Out (X : in out T) with Pre => True;

   function Pub (X : T) return Integer is
   begin
      return Read (X);  --  @INVARIANT_CHECK:PASS
   end Pub;

   function Priv (X : T) return Integer is
   begin
      return Read (X);  --  @INVARIANT_CHECK:FAIL
   end Priv;

   procedure Pub_In (X : T) is
   begin
      Read (X);  --  @INVARIANT_CHECK:PASS
   end Pub_In;

   procedure Priv_In (X : T) is
   begin
      Read (X);  --  @INVARIANT_CHECK:FAIL
   end Priv_In;

   procedure Pub_Out (X : out T) is
   begin
      Write (X);  --  @INVARIANT_CHECK:NONE
      Read_Write (X);  --  @INVARIANT_CHECK:PASS
      X := 0;
      Read_Write (X);  --  @INVARIANT_CHECK:FAIL
   end Pub_Out;

   procedure Priv_Out (X : out T) is
   begin
      Write (X);  --  @INVARIANT_CHECK:NONE
      Read_Write (X);  --  @INVARIANT_CHECK:PASS
      X := 0;
      Read_Write (X);  --  @INVARIANT_CHECK:FAIL
   end Priv_Out;

   procedure Pub_In_Out (X : in out T) is
   begin
      Read_Write (X);  --  @INVARIANT_CHECK:PASS
      X := 0;
      Read_Write (X);  --  @INVARIANT_CHECK:FAIL
   end Pub_In_Out;

   procedure Priv_In_Out (X : in out T) is
   begin
      Read_Write (X);  --  @INVARIANT_CHECK:FAIL
      X := 0;
      Read_Write (X);  --  @INVARIANT_CHECK:FAIL
   end Priv_In_Out;

end Type_Invariant_Legal_6;
