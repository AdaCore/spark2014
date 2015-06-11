function Late_Init return Positive is
   package Pkg is
      type T is private;
      function Get_Aaa (X : T) return Positive;
   private
      type T is record
         Aaa : Positive := Get_Aaa (T);
      end record;
      function Get_Aaa (X : T) return Positive is (X.Aaa);
   end Pkg;

   T_Var : Pkg.T;
begin
   return Pkg.Get_Aaa (T_Var);
end;
