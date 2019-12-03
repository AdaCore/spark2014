procedure P (X : Integer) is
   type T (D : Integer) is record
      C : Integer := T.D;
   end record;
begin
   null;
end;
