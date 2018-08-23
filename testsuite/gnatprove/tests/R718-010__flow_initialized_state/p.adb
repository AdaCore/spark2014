with Q;
package body P with Refined_State => (State => Set)
is
   Set : Q.T (D => 0);

   procedure Foo is null;

end P;
