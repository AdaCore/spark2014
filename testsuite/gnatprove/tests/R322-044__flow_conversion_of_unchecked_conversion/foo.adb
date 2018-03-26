with Ada.Unchecked_Conversion;

procedure Foo
is
   type UInt64 is mod 2**64;

   type Rec is record
      A : Integer;
      B : Integer;
   end record;

   function UCC is new Ada.Unchecked_Conversion
     (Source => UInt64,
      Target => Rec);

   Info : constant Rec := Rec (UCC (42));
begin
   null;
end Foo;
