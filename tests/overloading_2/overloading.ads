package Overloading
is
   function Sign (X: Integer) return Integer;
   function Sign (X: Float) return Integer ;
   function Abs_Add (A, B : in Integer) return Integer;
   function Abs_Add (A, B : in Float) return Float;
   procedure Abs_Eval(Eval : in out Boolean);
end Overloading;
