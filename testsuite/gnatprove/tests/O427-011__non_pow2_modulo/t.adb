procedure t
  with SPARK_Mode
is
   type U16 is mod 2**16;

   type M is mod 230;

   function MMin (X : M) return M
     with Post => MMin'Result = 229 - X + 1
   is
   begin
      return -X;
   end;

   function MAdd (X : M; Y : M) return M
     with Post => U16 (MAdd'Result) = (U16 (X) + U16 (Y)) mod 230
   is
   begin
      return X + Y;
   end;

   function MSub (X : M; Y : M) return M
     with Contract_Cases => (X = 0 and Y = 0 => MSub'Result = 0,
                             X /= 0 and Y = 0 => MSub'Result = X,
                             X = 0 and Y /= 0 => MSub'Result = -Y,
                             X = 2 and Y = 4 => MSub'Result = 228,
                             X = 4 and Y = 2 => MSub'Result = 2,
                             others => True)
   is
   begin
      return X - Y;
   end;

   function MMul (X : M; Y : M) return M
     with Post => U16 (MMul'Result) = (U16 (X) * U16 (Y)) mod 230
   is
   begin
      return X * Y;
   end;

begin
   null;
end t;
