procedure Test with SPARK_Mode is

   type Int_Acc is access Integer;

   C : constant Int_Acc := new Integer'(0);

   procedure P (Y : out Boolean) with
     Post => not Y;

   procedure P (Y : out Boolean) is
   begin
      Y := C = null;
      pragma Assert (C.all = 0); --  @ASSERT:FAIL
   end P;

   B : Boolean;
begin
   C.all := 15;
   P (B);
end Test;
