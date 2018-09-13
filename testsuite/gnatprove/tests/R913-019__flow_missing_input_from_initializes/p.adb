with Q;
package body P with Refined_State => (State => X)
is
   X : Integer := Q.Var;

   procedure Foo is null;
end P;
