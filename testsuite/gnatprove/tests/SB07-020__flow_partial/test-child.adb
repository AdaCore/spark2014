with Test.Child.User;

package body Test.Child
with Refined_State => (State => (Last_Allocated, Elems))
is

   package U is new Test.Child.User;

end Test.Child;
