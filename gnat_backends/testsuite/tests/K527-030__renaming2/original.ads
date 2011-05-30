package Original is
   function Opposite (X : Boolean) return Boolean with
     Post => Opposite'Result = not X;
end Original;
