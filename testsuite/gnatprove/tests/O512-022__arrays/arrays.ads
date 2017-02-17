package Arrays is
   type T is array (Positive range <>) of Positive;

   function Sum (X : T) return Natural with
     Post => Sum'Result >= X'Length,
     Contract_Cases => (X'Length = 0 => Sum'Result = 0,
                       (for all J in X'Range => X (J) = 0) => Sum'Result = 0), --  The guard here is equivalent to requiring X'Length = 0, as all elements of the array are positive
     Test_Case => (Name     => "small array",
                   Mode     => Nominal,
                   Requires => X'Length = 3),
     Test_Case => (Name     => "large sum",
                   Mode     => Nominal,
                   Ensures  => Sum'Result > 100_000),
     Test_Case => (Name     => "large array, small sum",
                   Mode     => Nominal,
                   Requires => X'Length > 100,
                   Ensures  => Sum'Result < 10);

   function Count_Even (X : T) return Natural with
     Post => Count_Even'Result <= X'Length,
     Contract_Cases => (X'Length = 0 => Count_Even'Result = 0),
     Test_Case => (Name     => "only odd",
                   Mode     => Nominal,
                   Requires => (for all J in X'Range => X (J) mod 2 = 1),
                   Ensures  => Count_Even'Result = 0),
     Test_Case => (Name     => "half even",
                   Mode     => Nominal,
                   Ensures  => X'Length in Count_Even'Result * 2
                                 .. Count_Even'Result * 2 + 1);

   function Count_Odd (X : T) return Natural;
end Arrays;
