pragma SPARK_Mode;
pragma Extensions_Allowed (On);
with Glob; use Glob;
procedure P
  with Global => (Output => G),
       Depends => (G => null)
is

   function F (X : in out Integer) return Integer
     with Side_Effects,
          Global => (Output => G),
          Pre => X < Integer'Last,
          Post => X = X'Old + 1
            and then F'Result = X
   is
   begin
      G := X;
      X := X + 1;
      return X;
   end F;
begin
   X : Integer := 0;
   Y : Integer := F(X);

   pragma Assert (X = Y);
end P;
