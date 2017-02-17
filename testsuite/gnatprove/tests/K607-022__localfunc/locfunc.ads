package Locfunc is
   procedure P (X : in out Integer)
      with Post => (X = 0);
end Locfunc;
