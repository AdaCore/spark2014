with Repro.A;

package Repro.B
is

   function F1 (Bar : Repro.A.Foo_Type) return Repro.A.String_Type
   is (Bar.X);

   type Bar_Type is new Repro.A.Foo_Type;

   function F2 (Bar : Bar_Type) return Repro.A.String_Type
   is (Bar.X);

end Repro.B;
