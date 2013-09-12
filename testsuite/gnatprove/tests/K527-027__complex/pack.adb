package body Pack is

   function PP1 return Boolean is

      X : T1;
   begin
      X.X := 1;
      return X.X > 0;
   end;

   function PP2 return Boolean is
      X : T2;
   begin
      X.X := new Integer'(1);
      return X.X.all > 0;
   end;

end;
