package Sorted with SPARK_Mode is
   type Nat_Array is array (Positive range 1 .. 100) of Natural;

   function Is_Sorted (A : Nat_Array) return Boolean is
  (for all I in A'Range =>
    (if I < A'Last then A (I) <= A (I + 1)));
   --  Returns True if A is sorted in increasing order.

   type Sorted_Nat_Array is private with
     Default_Initial_Condition => False;
   -- The implementation is private to avoid fiddling.

   function Open (A : Sorted_Nat_Array) return Nat_Array with
     Post => Is_Sorted (Open'Result);

   procedure Add (A : in out Sorted_Nat_Array; X : Natural);
private
   type Sorted_Nat_Array is new Nat_Array with
     Type_Invariant => Is_Sorted (Nat_Array (Sorted_Nat_Array));

   procedure Sort (A : in out Sorted_Nat_Array) with
     Post => Is_Sorted (A);
   -- The input of Sort may not be sorted.
end Sorted;
