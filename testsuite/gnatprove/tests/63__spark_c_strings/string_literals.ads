with Interfaces.C;         use Interfaces.C;

package String_Literals with SPARK_Mode is
   Foo_Foo : aliased constant char_array := "foo_foo" & nul;
   Bar     : aliased constant char_array := "bar" & nul & "bar";
end String_Literals;
