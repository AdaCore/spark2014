with Foo;
with Gen_Sub;
package Instance_Sub is
   function F return Integer is (Foo.G);

   G : Integer := 3;

   procedure Instance_Proc is new Gen_Sub (G, F);

end Instance_Sub;
