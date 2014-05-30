package dynamic_types with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   function Search (A : Nat_Array; C : Natural) return Natural with
     Pre  => A'First <= A'Last,
     Post => Search'Result = 0
     or else (Search'Result in A'Range and then A (Search'Result) = C);
end;
