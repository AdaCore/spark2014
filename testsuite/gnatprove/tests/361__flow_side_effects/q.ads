package Q is
   X : Boolean;
   function Init (Val : Boolean) return Boolean
      with Side_Effects, Global => (Output => X), Ghost;
end Q;
