function Id_Alias (X : Integer) return Integer
   with Post => Id_Alias'Result = X,
        Depends => (Id_Alias'Result => X)
is
   type R is record
      C : Integer;
   end record;

   Y : constant Integer := 123;  --  constant with no variable input
   Z : constant R with Import, Address => Y'Address;

begin
   return R'(Z with delta C => X).C;
end;
