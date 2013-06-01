package Search is
   subtype Position is Integer range 1 .. 10;
   type A is array (Position) of Integer;
   function Search (T : A; V : Integer) return Integer
      with Post =>
         ((if Search'Result = 0 then
          (for all Pos in T'First .. T'Last => T(Pos) /= V))
         and then
           (if T(Search'Result) = V then
            (for all Pos in T'First .. Search'Result - 1 => T(Pos) /= V)));
--            );
end Search;
