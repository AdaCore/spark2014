package body Sorted with SPARK_Mode is

   function Open (A : Sorted_Nat_Array) return Nat_Array is
      (Nat_Array (A));

   procedure Add (A : in out Sorted_Nat_Array; X : Natural) is
   begin
      A (10) := X;
      Sort (A);
   end Add;

   procedure Sort (A : in out Sorted_Nat_Array) with SPARK_Mode => Off is
   begin
      raise Program_Error;
   end Sort;
end sorted;
