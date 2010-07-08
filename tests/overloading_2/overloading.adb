package body Overloading
is

   function Sign (X : Integer) return Integer
   is
      V : Integer;
   begin
      if X > 0 then
         V := 1;
      elsif X < 0 then
         V := 2;
      else
         V := 0;
      end if;
      return V;
   end Sign;

   function Sign (X : Float) return Integer
   is
      V : Integer;
   begin
      if X > 0.0 then
         V := 1;
      elsif X < 0.0 then
         V := 2;
      else
         V := 0;
      end if;
      return V;
   end Sign;

   function Abs_Add (A, B : in Integer) return Integer
   is
      V : Integer;
   begin
      if (Sign (A) = 1) and (Sign (B) = 1) then
         V := A + B;
      elsif (Sign (A) = 1) and (Sign (B) = 2) then
         V := A - B;
      elsif (Sign (A) = 2) and (Sign (B) = 1) then
         V := B - A;
      else
         V := 0;
      end if;
      return V;
   end Abs_Add;

   function Abs_Add (A, B : in Float) return Float
   is
      V : Float;
   begin
      if (Sign (A) = 1) and (Sign (B) = 1) then
         V := A + B;
      elsif (Sign (A) = 1) and (Sign (B) = 2) then
         V := A - B;
      elsif (Sign (A) = 2) and (Sign (B) = 1) then
         V := B - A;
      else
         V := 0.0;
      end if;
      return V;
   end Abs_Add;

   procedure Abs_Eval (Eval      : in  Boolean;
                       Var_Int_1 : in out Integer;
                       Var_Int_2 : in out Integer;
                       Var_Re_1  : in out Float;
                       Var_Re_2  : in out Float;
                       Var_Out_1 :    out Integer;
                       Var_Out_2 :    out Float)
   is
      procedure Abs_Add
        (A, B : in Integer;
         C    : out Integer)
      is
      begin
         C := A + B;
      end Abs_Add;
   begin
      if Eval then
         Var_Int_1 := 10;
         Var_Int_2 := -20;
         Var_Re_1  := 10.0;
         Var_Re_2  := -20.0;
         Var_Out_1 := Abs_Add (Var_Int_1, Var_Int_2);
         Var_Out_2 := Abs_Add (Var_Re_1, Var_Re_2);
      else
         Abs_Add (Var_Int_1, Var_Int_2, Var_Out_1);
         Var_Out_2 := 0.0;
      end if;
   end Abs_Eval;

end Overloading;
