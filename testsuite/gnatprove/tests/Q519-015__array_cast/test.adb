Pragma SPARK_Mode(ON);

with cast_array; use cast_array;

procedure test is
   type Nat_Array is array (Positive range <>) of Natural;
   subtype Nat_Array1 is Nat_Array (1 .. 100);
   subtype Nat_Array2 is Nat_Array (1 .. 100);
   type Arr1 is array (1 .. 3) of Nat_Array1;
   type Arr2 is array (1 .. 3) of Nat_Array2;

   type Rec (X : Integer) is record
      Y : Integer;
   end record;
   subtype Rec1 is Rec (10);
   subtype Rec2 is Rec (10);
   type Arr3 is array (1 .. 3) of Rec1;
   type Arr4 is array (1 .. 3) of Rec2;

   X : Arr1 := (others => (others => 1));
   Y : Arr2 := Arr2 (X);
   W : Arr3 := (others => (X => 10, Y => 1));
   Z : Arr4 := Arr4 (W);

   test_array : Int_array1 := (1, 2, 3);
   result_array : Int_array2;
begin
   pragma Assert (for all I in Y'Range =>
                    (for all J in Y (I)'Range =>
                         Y (I) (J) = 1));
   pragma Assert (for all I in Z'Range => Z (I).Y = 1);
   result_array := Int_array2(test_array); --GNat OK, GNATprove error
   pragma Assert (result_array (1) = 2);
   result_array := cast (test_array);  --GNAT OK, GNATPROVE OK
   pragma Assert (result_array (1) = 2);
end test;
