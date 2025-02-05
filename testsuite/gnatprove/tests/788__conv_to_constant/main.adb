procedure Main with SPARK_Mode is
   type Int_Access is access Integer;
   type Int_Access_Constant is access constant Integer;

   function F return Int_Access_Constant is
      X3 : Int_Access := new Integer'(12); -- @RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   begin
      return Int_Access_Constant (X3); -- @RESOURCE_LEAK:FAIL
   end F;

   function F_2 return Int_Access_Constant is
   begin
      return new Integer'(12); -- @RESOURCE_LEAK:FAIL
   end F_2;

   X1 : Int_Access := new Integer'(12); -- @RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   Y1 : Int_Access_Constant := Int_Access_Constant (X1); -- @RESOURCE_LEAK:FAIL
   X2 : Int_Access := new Integer'(12); -- @RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   Y2 : Int_Access_Constant;
   Y3 : Int_Access_Constant := new Integer'(12); -- @RESOURCE_LEAK:FAIL
   Y4 : Int_Access_Constant;
begin
   Y2 := Int_Access_Constant (X2); -- @RESOURCE_LEAK:FAIL
   Y2 := new Integer'(12); -- @RESOURCE_LEAK:FAIL
end Main;
