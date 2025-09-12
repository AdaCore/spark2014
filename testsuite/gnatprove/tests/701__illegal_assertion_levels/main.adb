pragma Assertion_Level (Silver);
pragma Assertion_Level (Gold, Depends => Silver);
procedure Main with spark_mode is
   type Int_Acc is access Integer;

   procedure Test_Policy is
      pragma Assertion_Policy (Ghost => Check);
      X : Int_Acc := new Integer'(12) with Ghost;
      pragma Assertion_Policy (Ghost => Ignore);
      Y : Int_Acc := X with Ghost;
      --  This should be rejected, X is moved into disabled ghost code

      pragma Assertion_Policy (Ghost => Check);
      Z : Int_Acc := new Integer'(12) with Ghost;
      pragma Assertion_Policy (Ghost => Ignore);
      procedure Set_To_Zero (X : not null Int_Acc) with
        Global => null,
	Ghost;

      procedure Set_To_Zero (X : not null Int_Acc) is
      begin
        X.all := 0;
      end;
   begin
      Set_To_Zero (Z);
      --  This should be rejected, Z is moved into disabled ghost code
   end;

   procedure Test_Levels is
      X : Int_Acc := new Integer'(12) with Ghost => Silver;
      Y : Int_Acc := X with Ghost => Gold;
      --  This should be rejected, levels should match

      Z : Int_Acc := new Integer'(12) with Ghost => Silver;
      procedure Set_To_Zero (X : not null Int_Acc) with
        Global => null,
	Ghost  => Gold;

      procedure Set_To_Zero (X : not null Int_Acc) is
      begin
        X.all := 0;
      end;
   begin
      Set_To_Zero (Z);
      --  This should be rejected, levels should match
   end;

begin
   null;
end Main;
