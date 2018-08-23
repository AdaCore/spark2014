with Q;
package body P with Refined_State => (State => Set)
is
   package Inst is new Q;

   Set : Inst.T (D => 0);

   procedure Foo is null;

end P;
