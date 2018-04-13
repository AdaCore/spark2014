with B;

package A.Main
is
   procedure P (Y :    out T)
     with Pre => B.Get;
end A.Main;
