with P.Child;
package body P with Refined_State => (State1 => (A, B),
                                      State2 => P.Child.C)
is
   A, B : Integer := 0;
   procedure Foo is null;
end P;
