package Base is
   type Base_T is tagged private;
   function Make (B : Boolean) return Base_T;
private
   type Base_T is tagged record
      A : Boolean;
   end record;
end Base;
