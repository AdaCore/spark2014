package body P is
   function Increment (X : Integer) return Integer is
   begin
      return X + 1;
   end Increment;
   function Decrement (X : Integer) return Integer is
   begin
      return X - 1;
   end Decrement;
end P;
