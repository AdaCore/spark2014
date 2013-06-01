procedure P (X : Integer) is
   function F5 (X : Integer) return Boolean is
   begin
      return X > 0;
   end F5;
begin
   pragma Assert (F5 (3) = F5 (3));
   null;
end P;
