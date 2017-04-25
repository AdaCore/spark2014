with Q;

package P is

   X : Boolean := Q.X;
   function P return Boolean
      with Post => P'Result = Q.X;
end P;
