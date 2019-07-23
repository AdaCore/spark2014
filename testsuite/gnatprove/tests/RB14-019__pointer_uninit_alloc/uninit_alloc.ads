package Uninit_Alloc with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   type Nat_Array_Ptr is access Nat_Array;

   type Null_Record (D : Integer) is null record;

   type Null_Record_Ptr is access Null_Record;

   X : Nat_Array_Ptr := new Nat_Array (1 .. 2);

   Y : Null_Record_Ptr := new Null_Record (5);
end Uninit_Alloc;
