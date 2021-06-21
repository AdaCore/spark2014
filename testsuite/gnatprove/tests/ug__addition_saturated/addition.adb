function Addition (X, Y : Integer) return Integer with
  SPARK_Mode,
  Contract_Cases => ((X + Y in Integer)    => Addition'Result = X + Y,
                     X + Y < Integer'First => Addition'Result = Integer'First,
                     X + Y > Integer'Last  => Addition'Result = Integer'Last)
is
begin
   if X < 0 and Y < 0 then -- both negative
      if X < Integer'First - Y then
         return Integer'First;
      else
         return X + Y;
      end if;

   elsif X > 0 and Y > 0 then -- both positive
      if X > Integer'Last - Y then
         return Integer'Last;
      else
         return X + Y;
      end if;

   else -- one positive or null, one negative or null, adding them is safe
      return X + Y;
   end if;
end Addition;
