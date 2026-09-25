with Foo;
with Lib_Pkg;
with Lib_Subp;

procedure Main with SPARK_Mode is
   procedure My_Bar is new Foo.Bar;
   procedure My_Baz is new Foo.Baz;
   package My_Gen is new Foo.Gen;
   procedure My_Unrelated is new Foo.Unrelated;
   procedure My_Lib_Subp is new Lib_Subp;
   package My_Lib_Pkg is new Lib_Pkg;
begin
   null;
end Main;
