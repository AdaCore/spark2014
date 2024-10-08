pragma Extensions_Allowed (On);

procedure Test_BC (B : Boolean) with SPARK_Mode is

   type Int_Acc is access Integer;

   function Raise_Exp (B : Boolean) return Integer with
     Side_Effects,
     Post => not B,
     Exceptional_Cases => (Program_Error => B);

   function Raise_Exp (B : Boolean) return Integer is
   begin
      if B then
         raise Program_Error;
      else
         return 1;
      end if;
   end Raise_Exp;

   Y : Int_Acc := new Integer'(14);
   X : Int_Acc;
begin
   X := Y;
   I : Integer := Raise_Exp (B);
   Y := null;
exception
   when Program_Error =>
      pragma Assert (Y = null); --  Y is be moved here
end Test_BC;
