package Q is
   V : Integer := 0;
   type T (D : Integer := V) is private;
private
   type T (D : Integer := V) is null record;
   --  Variable input in default expression, should be rejected
   --  Flow should only emit one error, as both default expressions reference
   --  the same variable input.
end;
