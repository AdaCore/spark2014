package P
  with SPARK_Mode
is

   function Is_Prime (X : Positive) return Boolean is
      (X = 2 or else (for all V in 2 .. X-1 => X mod V /= 0));

   pragma Assert (Is_Prime (23));
   pragma Assert (Is_Prime (37));
   pragma Assert (Is_Prime (53));

end P;
