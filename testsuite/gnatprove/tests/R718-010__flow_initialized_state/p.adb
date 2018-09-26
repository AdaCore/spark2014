with Q;
package body P with Refined_State => (State => (Set1, Set2))
is
   Set1 : Q.T1 (D => 0);
   Set2 : Q.T2;

   procedure Foo is null;

end P;
