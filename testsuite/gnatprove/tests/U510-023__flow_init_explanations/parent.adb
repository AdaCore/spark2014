private with Parent.Child;

package body Parent with
  Refined_State => (State => Child.X)
is
end Parent;
