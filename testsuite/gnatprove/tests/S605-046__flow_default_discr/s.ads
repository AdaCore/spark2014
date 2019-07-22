package S is
   V : Integer := 0;
   type T;
   type T (D : Integer := V) is null record;
end;
