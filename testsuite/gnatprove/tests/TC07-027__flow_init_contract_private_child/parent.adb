with Parent.Child;
package body Parent with Refined_State => (A => (Father, Parent.Child.B)) is
   Father : Boolean := True;
   procedure Dummy is null;
end Parent;
