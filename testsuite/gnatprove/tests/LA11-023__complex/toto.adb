with Foo; use Foo;

procedure Toto is

   function Exp (X : Imaginary) return Integer is
      ImX : constant Float'Base := Im (X);

   begin
      return 1;
   end Exp;
begin
   null;

end Toto;
