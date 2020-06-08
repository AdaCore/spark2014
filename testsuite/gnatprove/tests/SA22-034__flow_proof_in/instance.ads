with Test;
with Test.Child;

package Instance
is

   package T is new Test (Size => 100);
   package C is new T.Child;

end Instance;
