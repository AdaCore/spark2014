package body Q is
   type T is new R (False);

   procedure Dummy is null;
   function Foo (A : R) return T is
   begin
      return T (A);
   end Foo;
end Q;
