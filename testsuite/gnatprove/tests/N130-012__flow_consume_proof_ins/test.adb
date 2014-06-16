package body Test
  with Refined_State => (State => (Foo, Bar))
is
   Foo, Bar : Integer := 0;

   procedure Rotate (X, Y, Z : in out Integer)
   is
      Tmp : Integer := X;
   begin
      X := Z;
      Z := Y;
      Y := Tmp;
   end Rotate;

   function Some_Func return Integer is (Foo)
     with Refined_Global => Foo;

   procedure Some_Proc (X : in out Integer)
     with Refined_Global => Foo,
          Refined_Post   => X >= Foo
   is
   begin
      if X < Foo then
         X := Foo + 1;
      end if;
   end Some_Proc;
end Test;
