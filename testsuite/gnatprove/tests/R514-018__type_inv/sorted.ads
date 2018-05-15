package Sorted with SPARK_Mode is
   type Nat_Array is array (Positive range 1 .. 100) of Natural;

   function Is_Sorted (A : Nat_Array) return Boolean is
  (for all I in A'Range =>
    (if I < A'Last then A (I) <= A (I + 1)));
   --  Returns True if A is sorted in increasing order.

   type Sorted_Nat_Array is private;
   -- The implementation is private to avoid fiddling.

   function Open (A : Sorted_Nat_Array) return Nat_Array with
     Post => Is_Sorted (Open'Result);
private
   type Sorted_Nat_Array is new Nat_Array with
     Type_Invariant => Is_Sorted (Sorted_Nat_Array);

   function Open (A : Sorted_Nat_Array) return Nat_Array is
      (Nat_Array (A));
end sorted;
