procedure Test is
   function Id (X : Integer) return Integer
   is (X)
     with Post => True;
begin
   pragma Assert (Id (1) = 1);
end Test;
