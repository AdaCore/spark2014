with Gen;

pragma Elaborate_All (Gen);

package Foo with Elaborate_Body
is

   package Gnp is new Gen (T => Positive);
   use Gnp;

end Foo;
