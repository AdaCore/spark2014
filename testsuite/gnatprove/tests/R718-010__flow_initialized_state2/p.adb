with Q;
package body P with Refined_State => (State => X)
is

   type TT is record
      Set : Q.T;
      Z   : Integer;
   end record;

   X : TT;

   procedure Foo is null;
begin
   X.Z := 0;
end P;
