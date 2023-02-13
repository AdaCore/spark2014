package Randpack is
   function Rand (X : Integer) return Integer with
     Import,
     Post => Rand'Result in 1 .. 10;

end Randpack;
