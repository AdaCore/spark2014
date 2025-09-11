procedure P with SPARK_Mode is
   type Int_Acc is access Integer;
      pragma Assertion_Policy (Assert => Check);

   procedure Test1 is
      pragma Assertion_Policy (Ghost => Check);
      X : Int_Acc := new Integer'(12) with Ghost;
   begin
      declare
         pragma Assertion_Policy (Ghost => Ignore);
         Y : access Integer := X with Ghost; --  This should be rejeted
      begin
         Y.all := 0;
      end;
      pragma Assert (X.all = 0); --  This assert will fail at runtime
   end Test1;

   procedure Test2 is
      pragma Assertion_Policy (Ghost => Check);
      X : Int_Acc := new Integer'(12) with Ghost;
   begin
      declare
         pragma Assertion_Policy (Ghost => Ignore);
         procedure Set_To_Zero (X : not null access Integer) with
           Ghost,
           Post => X.all = 0;
         procedure Set_To_Zero (X : not null access Integer) is
         begin
            X.all := 0;
         end Set_To_Zero;
      begin
         Set_To_Zero (X); --  This should be rejeted
      end;
      pragma Assert (X.all = 0); --  This assert will fail at runtime
   end Test2;

begin
   null;
end;
