procedure Membership_2 with SPARK_Mode is
    type Nat_Array is array (Positive range <>) of Natural;

    type Ptr is access Nat_Array;

    subtype Ptr2 is Ptr (1 .. 5);

    X : Ptr2 := new Nat_Array'(1 .. 5 => 0);
    Y : Ptr := new Nat_Array'(1 .. 5 => 0);
begin
    if Y in X | Y then
       pragma Assert (False);
    end if;
end Membership_2;
