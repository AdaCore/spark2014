procedure Illegal is

   type Int is range 1 .. 10 with
     Annotate => (GNATprove, No_Bitwise_Operations);

   type New_Int is new Integer with
     Annotate => (GNATprove, No_Bitwise_Operations);

   type Uns is mod 2**32;
   subtype Sub is Uns with
     Annotate => (GNATprove, No_Bitwise_Operations);

   type Base is mod 2**32 with
     Annotate => (GNATprove, No_Bitwise_Operations);
   pragma Provide_Shift_Operators (Base);

   X, Y : Base := 1;
begin
   X := X xor Y;
   X := X or Y;
   X := X and Y;
   X := not X;
   X := Shift_Left (X, 2);
   X := Shift_Right (X, 2);
   X := Shift_Right_Arithmetic (X, 2);
   X := Rotate_Left (X, 2);
   X := Rotate_Right (X, 2);
end;
