package Math is

   function Sqrt (X : Integer) return Integer with
     Pre  => X >= 0,
     Post => Sqrt'Result >= 0,
     Contract_Cases => (X = 0 => Sqrt'Result = 0,
                        X > 0 => Sqrt'Result > 0);

   function Bad (X : Integer) return Integer with
     Pre  => X >= 0,
     Post => Bad'Result >= 0,
     Contract_Cases => (X + X = 0 => Bad'Result = 0,
                        X > 0     => Bad'Result > 0);

end Math;
