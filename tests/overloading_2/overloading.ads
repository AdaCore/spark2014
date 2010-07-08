package Overloading
is
   function Sign (X: Integer) return Integer;
   function Sign (X: Float) return Integer ;
   function Abs_Add (A, B : in Integer) return Integer;
   function Abs_Add (A, B : in Float) return Float;
   procedure Abs_Eval (Eval      : in     Boolean;
                       Var_Int_1 : in out Integer;
                       Var_Int_2 : in out Integer;
                       Var_Re_1  : in out Float;
                       Var_Re_2  : in out Float;
                       Var_Out_1 :    out Integer;
                       Var_Out_2 :    out Float);
end Overloading;
