procedure Main is
   package P is
      type A is private;
      type B is private;
   private
      type A is new Integer with Predicate => B (A) in B;
      type B is new Integer with Predicate => A (B) in A;

      X : A := 0;
   end;
begin
   null;
end;
