package Math is

   function Sqrt (X : Integer) return Integer with
     Pre  => X >= 0,
     Post => Sqrt'Result >= 0,
     Contract_Case => (Name     => "zero",
                       Mode     => Nominal,
                       Requires => X = 0,
                       Ensures  => Sqrt'Result = 0),
     Contract_Case => (Name     => "non zero",
                       Mode     => Nominal,
                       Requires => X > 0,
                       Ensures  => Sqrt'Result > 0);

   function Bad (X : Integer) return Integer with
     Pre  => X >= 0,
     Post => Bad'Result >= 0,
     Contract_Case => (Name     => "zero",
                       Mode     => Nominal,
                       Requires => X + X = 0,
                       Ensures  => Bad'Result = 0),
     Contract_Case => (Name     => "non zero",
                       Mode     => Nominal,
                       Requires => X > 0,
                       Ensures  => Bad'Result > 0);

end Math;
