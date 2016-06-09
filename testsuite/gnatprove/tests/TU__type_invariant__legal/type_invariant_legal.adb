package body Type_Invariant_Legal is

   procedure Priv_In (X : T);
   procedure Priv_Out (X : out T);
   procedure Priv_In_Out (X : in out T);

   function Pub return T is
   begin
      return 0;  --  @INVARIANT_CHECK:FAIL
   end Pub;

   function Priv return T is
   begin
      return 0;  --  @INVARIANT_CHECK:NONE
   end Priv;

   procedure Pub_In (X : T) is
   begin
      return;  --  @INVARIANT_CHECK:NONE
   end Pub_In;

   procedure Priv_In (X : T) is
   begin
      return;  --  @INVARIANT_CHECK:NONE
   end Priv_In;

   procedure Pub_Out (X : out T) is
   begin
      X := 1;
      return;  --  @INVARIANT_CHECK:PASS
   end Pub_Out;

   procedure Priv_Out (X : out T) is
   begin
      X := 1;
      return;  --  @INVARIANT_CHECK:NONE
   end Priv_Out;

   procedure Pub_In_Out (X : in out T) is
   begin
      X := X - 1;  --  @RANGE_CHECK:PASS
      return;  --  @INVARIANT_CHECK:FAIL
   end Pub_In_Out;

   procedure Priv_In_Out (X : in out T) is
   begin
      X := X - 1;  --  @RANGE_CHECK:FAIL
      return;  --  @INVARIANT_CHECK:FAIL
   end Priv_In_Out;

end Type_Invariant_Legal;
