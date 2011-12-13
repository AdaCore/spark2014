package Old is

   function Id (X : Integer) return Integer is (X);

   Z : Integer;

   subtype Smaller is Integer range 1 .. 10;

   procedure Nothing
      with Post => (Id (Z) = Id (Z)'Old);

   procedure Range_Expr (X : Integer)
      with Post => (Boolean'(X  in Smaller'Range)'Old);
end Old;
