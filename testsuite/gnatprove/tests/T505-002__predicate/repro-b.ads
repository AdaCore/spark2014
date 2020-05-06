with Repro.A;

package Repro.B
is

   type Bar_Type is private;

   function F1 (Bar : Repro.A.Foo_Type) return Repro.A.String_Type;

private

   type Bar_Type is new Repro.A.Foo_Type;

   function F (Bar : Bar_Type) return Repro.A.String_Type
   is (Bar.X);

end Repro.B;
