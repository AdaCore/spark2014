package body Base is
   function Make (B : Boolean) return Base_T is
   begin
      return Base_T'(A => B);
   end Make;
end Base;
