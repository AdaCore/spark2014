package body Overloading
is

   function Sign (X : Integer) return Integer is
   begin
      if X > 0 then
         return +1;
      elsif X < 0 then
         return -1;
      else
         return 0;
      end if;
   end Sign;

   function Sign (X : Float) return Integer is
   begin
      if X > 0.0 then
         return +1;
      elsif X < 0.0 then
         return -1;
      else
         return 0;
      end if;
   end Sign;

   function Abs_Add (A, B : in Integer) return Integer
   is
   begin
      if (Sign (A) = +1) and (Sign (B) = +1) then
         return A + B;
      elsif (Sign (A) = +1) and (Sign (B) = -1) then
         return A - B;
      elsif (Sign (A) = -1) and (Sign (B) = +1) then
         return B - A;
      else
         return 0;
      end if;
   end Abs_Add;

   function Abs_Add (A, B : in Float) return Float
   is
   begin
      if (Sign (A) = +1) and (Sign (B) = +1) then
         return A + B;
      elsif (Sign (A) = +1) and (Sign (B) = -1) then
         return A - B;
      elsif (Sign (A) = -1) and (Sign (B) = +1) then
         return B - A;
      else
         return 0.0;
      end if;
   end Abs_Add;

   procedure Abs_Eval (Eval : in out Boolean)
   is
      procedure Abs_Add
        (A, B : in Integer;
         C    : out Integer)
      is
      begin
         C := A + B;
      end Abs_Add;

      Var_Out_1 : Integer;
      Var_Out_2 : Float;
      Var_Int_1 : Integer := 10;
      Var_Int_2 : Integer := -20;
      Var_Re_1 : Float := 10.0;
      Var_Re_2 : Float := -20.0;
   begin
      if Eval then
         Var_Out_1 := Abs_Add (Var_Int_1, Var_Int_2);
         Var_Out_2 := Abs_Add (Var_Re_1, Var_Re_2);
      else
	Abs_Add (Var_Int_1, Var_Int_2, Var_Out_1);
      end if;
   end Abs_Eval;


end Overloading;
