package P is
   V : Integer := 0;
   type T is private;
private
   type T (D : Integer := V) is null record;
   --  Variable input in default expression, should be rejected
end;
