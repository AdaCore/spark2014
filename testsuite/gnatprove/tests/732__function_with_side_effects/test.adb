procedure Test with SPARK_Mode is
   type Int_Acc is access Integer;

   --  Test functions with deep OUT parameters

   function Set (X : out Int_Acc) return Integer with
     Side_Effects,
     Post => X /= null and then X.all = Set'Result;

   function Set (X : out Int_Acc) return Integer is
   begin
      X := new Integer'(12); -- @RESOURCE_LEAK:PASS
      return 12;
   end Set;

   procedure Test_1 with Global => null is
      X : Int_Acc := new Integer'(12);
      Y : Int_Acc := X;
      I : Integer;
   begin
      I := Set (X); -- @RESOURCE_LEAK:PASS
      pragma Assert (X.all = I);
   end Test_1;

   procedure Test_2 with Global => null is
      X : Int_Acc := new Integer'(12);
      I : Integer;
   begin
      I := Set (X); -- @RESOURCE_LEAK:FAIL
      pragma Assert (X.all = I);
   end Test_2;

   --  Test functions with deep global outputs

   X : Int_Acc;

   function Set_X return Integer with
     Global => (Output => X),
     Side_Effects,
     Post => X /= null and then X.all = Set_X'Result;

   function Set_X return Integer is
   begin
      X := new Integer'(12); -- @RESOURCE_LEAK:PASS
      return 12;
   end Set_X;

   procedure Test_3 with Global => (Output => X) is
      I : Integer;
   begin
      I := Set_X; -- @RESOURCE_LEAK:PASS
      pragma Assert (X.all = I);
   end Test_3;

   procedure Test_4 with Global => (In_Out => X) is
      I : Integer;
   begin
      I := Set_X; -- @RESOURCE_LEAK:FAIL
      pragma Assert (X.all = I);
   end Test_4;

begin
   null;
end Test;
