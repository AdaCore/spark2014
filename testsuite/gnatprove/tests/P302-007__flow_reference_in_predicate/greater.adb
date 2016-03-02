function Greater (X, Y : Integer) return Boolean is
   package P is
      subtype T is Integer with Dynamic_Predicate => T > Y;
   end;
begin
   return X in P.T;
end;
