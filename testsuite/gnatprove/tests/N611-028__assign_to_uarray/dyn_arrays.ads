package Dyn_Arrays with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;
   Max : constant natural := 100;
   subtype Nat_Array_Max is Nat_Array (1 .. Max);

   procedure Copy (From : Nat_Array_Max; To : out Nat_Array) with
     Pre  => To'Last >= To'First and then To'Last - To'First = 99,
     Post => (for all I in To'Range =>
                To (I) = From (I - To'First + 1));

   procedure Copy_Bad (From : Nat_Array_Max; To : out Nat_Array) with
     Pre  => To'Last >= To'First and then To'Last - To'First = 99,
     Post => (for all I in From'Range => -- @POSTCONDITION:FAIL
                (if I in To'Range then To (I) = From (I)));
end;
