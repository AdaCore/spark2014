package P_Max_Array with SPARK_Mode is
   subtype Index_Range is Integer range 1 .. 100;
   type Nat_Array is array (Index_Range range <>) of Natural;

   function Max_Array_1 (A, B : Nat_Array) return Nat_Array with
     Pre => A'Length = B'Length;

   function Max_Array_2 (A, B : Nat_Array) return Nat_Array with
     Pre  => A'Length = B'Length,
     Post => (for all K in A'Range =>
                (if A (K) > B (K - A'First + B'First) then
                     Max_Array_2'Result (K) = A (K)
                 else Max_Array_2'Result (K) = B (K - A'First + B'First)));

   procedure Max_Array_3 (A : in out Nat_Array; B : Nat_Array) with
     Pre  => A'Length = B'Length,
     Post => (for all K in A'Range =>
                (if A'Old (K) > B (K - A'First + B'First) then
                     A (K) = A'Old (K)
                 else A (K) = B (K - A'First + B'First)));
end P_Max_Array;
