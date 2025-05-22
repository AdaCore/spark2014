with Ada.Unchecked_Conversion;
procedure Cover with spark_mode is

  type U32 is mod 2 ** 32;
  X : Integer with Size => 32;

  Z : U32 with Address => X'Address, Import, Size => 32;

  type Rec is record
    Z : U32;
  end record;

  Obj : Rec;

  Obj2 : U32 with Address => Obj.Z'Address, Import;

begin
   pragma Assert (Z >= 0);
end;
