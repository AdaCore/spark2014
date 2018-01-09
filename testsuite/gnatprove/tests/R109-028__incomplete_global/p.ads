with Q;

package P is

   function F return Boolean with Pre => Q.Unknown and False, Global => null;
   --  The precondition can't be satisfied, no matter what. Indeed, without
   --  the Global contract (which is WRONG, because it misses the Q.X coming
   --  from the generated global of Q.Unknown), we get some unproved checks.

end;
