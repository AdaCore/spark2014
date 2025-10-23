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
         Y : Integer with Import, Address => X'Address, Alignment => 4; --  X is moved, it cannot be read
      begin
         Y := 16;
      end;
      pragma Assert (B.all = 15);
   end P2;

   procedure P3 with Global => null is
      type Int_Acc is access all Integer;
      X : aliased Integer := 15 with Alignment => 4;
      B : access constant Integer := X'Access;
   begin
      declare
         Y : Integer with Import, Address => X'Address, Alignment => 4; --  X is observed, reading it is ok
      begin
         Y := 16; --  X is observed, it cannot be assigned
      end;
      pragma Assert (B.all = 15);
   end P3;

   procedure P4 with Global => null is
      type Int_Acc is access all Integer;
      X : aliased Integer := 15 with Alignment => 4;
      B : access constant Integer := X'Access;
   begin
      declare
         Y : Integer := 12 with Address => X'Address, Alignment => 4; --  X is observed, it cannot be assigned
      begin
         Y := 16;
      end;
      pragma Assert (B.all = 15);
   end P4;
begin
   null;
end;
