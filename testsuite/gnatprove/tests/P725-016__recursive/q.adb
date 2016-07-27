with P; use P;
package body Q is
   function S return Boolean is
       X : Integer := 0;
   begin
      return X in P.T;
   end;
end Q;
