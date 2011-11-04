package Search is
   subtype Position is Integer range 1 .. 10;
   type A is array (Position) of Integer;
   function No_V_In_Range (T : A; V : Integer; Low,Up : Position)
     return Boolean is (for all Pos in Low .. Up => T(Pos) /= V);
   function Search (T : A; V : Integer) return Integer
      with Post =>
        ((Search'Result = 0 and then No_V_In_Range(T,V,T'First,T'Last))
         or else
           (T(Search'Result) = V and then
              No_V_In_Range(T,V,T'First,Search'Result-1)));
end Search;
