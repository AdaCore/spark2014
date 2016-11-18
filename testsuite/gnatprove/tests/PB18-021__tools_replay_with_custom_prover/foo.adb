procedure Foo (X : in out Boolean;
               Y : in out Boolean)
with Post => X = Y'Old and Y = X'Old
is
begin
   X := X xor Y;
   Y := X xor Y;
   X := X xor Y;
end Foo;
