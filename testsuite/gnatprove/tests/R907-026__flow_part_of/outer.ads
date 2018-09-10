private with Inner;

generic

package Outer
with
   Abstract_State => null
is

private

   package Inner_Package is new Inner;

end Outer;
