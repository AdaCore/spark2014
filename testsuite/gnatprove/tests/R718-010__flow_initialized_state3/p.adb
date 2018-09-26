with Q;
package body P with Refined_State => (State => X)
is
   type T is record
      Y : Integer;
      Z : Integer := 0;
   end record;

   X : T;

   procedure Foo is null;
begin
   X.Y := 0;
end P;
