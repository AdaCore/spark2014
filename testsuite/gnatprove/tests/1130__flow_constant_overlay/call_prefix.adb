function Call_Prefix (J : Integer) return Character
   with Depends => (Call_Prefix'Result => J)
is
   function Foo (X : Integer) return Character with Import;
   Y : constant Character with Import, Address => Foo (J)'Address;
begin
   return Y;
end;
