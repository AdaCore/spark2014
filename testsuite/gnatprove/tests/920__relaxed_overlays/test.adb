procedure Test with SPARK_Mode is
  type T is record
   N : Natural;
   B : Boolean;
 end record
   with Relaxed_Initialization, Size => 32, Object_Size => 32;

  type U is mod 2 ** 32;

  X1 : T;
  Y1 : U := 0 with Address => X1'Address;
  X2 : U := 0;
  Y2 : T with Address => X2'Address, Import;
begin
  null;
end Test;
