package R is
   X : Boolean with Constant_After_Elaboration;
   function Init (Val : Boolean) return Boolean with Side_Effects;
end R;
