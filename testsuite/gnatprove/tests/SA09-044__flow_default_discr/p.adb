procedure P (Value : Integer; Result : out Integer)
  with Depends => (Result => Value),
       Post    => Result = Value
is

   type T (D : Integer) is record
      C : Integer := D;
   end record;

   Hack : T (Value);

begin
   Result := Hack.C;
end;
