package P with Abstract_State => State is
   function Init (Val : Boolean) return Boolean
      with Side_Effects, Global => (Output => State);
end P;
