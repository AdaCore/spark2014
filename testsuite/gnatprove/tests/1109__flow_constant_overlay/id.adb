function Id (X : Integer) return Integer
   with Post => Id'Result = X,
        Depends => (Id'Result => X)
is
   type R is record
      C : Integer;
   end record;

   Y : constant R := (C => 123);  --  constant with no variable input

begin
   return R'(Y with delta C => X).C;
end;
