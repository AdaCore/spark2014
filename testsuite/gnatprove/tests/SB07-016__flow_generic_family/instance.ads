with Test;
with Test.Child;
with Test.Child.User;

package Instance
is
   package T is new Test
     (Size => 200);

   package TC is new T.Child;
   package TCU is new TC.User;

end Instance;
