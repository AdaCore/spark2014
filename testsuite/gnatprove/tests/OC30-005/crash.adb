procedure Crash
   with SPARK_Mode => On
is

   function Func_1 (X : Float)
   return Float
   is
      X_New : Float;
   begin
      X_New := X * 2.0;
      return X_New;
   end Func_1;

   function Expression_Func (Value : Float) return Float
   is
      (Func_1 (Value));

begin
   null;
end Crash;
