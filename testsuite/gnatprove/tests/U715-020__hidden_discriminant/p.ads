package P is
   type B (D : Integer) is null record;
   type T is private;

private

   type T (U : Integer := 0) is new B (U);

   subtype S is T (0);

   V : S;

end P;
