procedure Main with SPARK_Mode is
   procedure P1 with Global => null is
      type Int_Acc is access all Integer;
      X : Integer := 15 with Alignment => 4;
      Y : aliased Integer with Import, Address => X'Address, Alignment => 4;
   begin
      declare
         B : Int_Acc := Y'Access;
      begin
         B.all := 16;
      end;
      pragma Assert (X = 15); --  X should be moved too
   end P1;

   procedure P2 with Global => null is
      type Int_Acc is access all Integer;
      X : aliased Integer := 15 with Alignment => 4;
      B : Int_Acc := X'Access;
   begin
      declare
         Y : Integer with Import, Address => X'Address, Alignment => 4; --  X should be moved
      begin
         Y := 16;
      end;
      pragma Assert (B.all = 15);
   end P2;
begin
   null;
end;
