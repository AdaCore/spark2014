procedure Membership with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   type Ptr is access Nat_Array;

   subtype Ptr2 is Ptr (1 .. 5);

   X : Ptr2 := new Nat_Array'(1 .. 5 => 0);
   Y : Ptr := new Nat_Array'(1 .. 6 => 0);
begin
   pragma Assert (X in Ptr);
   pragma Assert (Y in Ptr2); --@ASSERT:FAIL
end Membership;
