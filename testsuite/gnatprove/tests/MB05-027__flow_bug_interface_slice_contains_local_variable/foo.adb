procedure Foo (V : out Integer)
with
   Global  => null,
   Depends => (V => null)
is
   type R (Blah : Boolean := False) is record
      X : Integer;
   end record;
   pragma Warnings (Off, "unused variable ""Tmp""");
   Tmp : R;
begin
   V := 12;
end Foo;
