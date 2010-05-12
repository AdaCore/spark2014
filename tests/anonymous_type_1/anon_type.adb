package body Anon_Type is
   function Increment(Var_In :  in Integer) return Integer
   is
      Var_Out : Integer range 0 .. 10;
   begin
      Var_Out  := Var_In + 1;
      return Var_Out;
   end Increment;
end Anon_Type;
