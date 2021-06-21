with Aliasing; use Aliasing;

procedure Check_Param_Aliasing with
  SPARK_Mode
is
   X, Y, Z : Integer := 0;
begin
   Whatever (In_1 => X, In_2 => X, Out_1 => X, Out_2 => X);  --  illegal
   Whatever (In_1 => X, In_2 => X, Out_1 => X, Out_2 => Y);  --  correct
   Whatever (In_1 => X, In_2 => X, Out_1 => Y, Out_2 => X);  --  correct
   Whatever (In_1 => Y, In_2 => Z, Out_1 => X, Out_2 => X);  --  illegal
end Check_Param_Aliasing;
