package Bug with
  Spark_Mode is

   type T is new Integer;

   type T_Arr is array (Positive range <>) of T;

   function Is_Equal
     (A    : T_Arr;
      B    : T_Arr;
      Size : Natural) return Boolean is
     (for all I in 0 .. Size - 1 => A (A'First + I) = B (B'First + I)) with
     Pre => (Size <= A'Length and Size <= B'Length),
     Ghost;

   function Has_Sub_Range
     (A      : T_Arr;
      Size_A : Natural;
      B      : T_Arr;
      Size_B : Natural) return Boolean is
     (for some I in 0 .. Size_A - Size_B => Is_Equal(A(A'First + I .. A'Last), B, Size_B)) with
       Pre => Size_A <= A'Length and then
              Size_B <= B'Length,
       Ghost;

   function Search
     (A      : T_Arr;
      Size_A : Natural;
      B      : T_Arr;
      Size_B : Natural) return Natural with
     Pre  => Size_A <= A'Length and then
             Size_B <= B'Length,
     Post => Search'Result <= Size_A - Size_B,
     Contract_Cases =>
       (Has_Sub_Range(A, Size_A, B, Size_B) =>
          Is_Equal(A(A'First + Search'Result .. A'Last), B, Size_B),
        others                              =>
          Search'Result = Size_A
       );
end Bug;
