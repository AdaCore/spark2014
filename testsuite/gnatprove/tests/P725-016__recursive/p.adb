package body P is

   function F return Boolean is
      X : Integer := 0;
   begin
      return X in T;
   end;

end P;
