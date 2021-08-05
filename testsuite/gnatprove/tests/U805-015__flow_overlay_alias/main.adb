procedure Main is
   type T is limited record
      C : Integer;
   end record;
   for T'Object_Size use Integer'Size;

   X : T := (C => 1) with Alignment => Integer'Alignment;
   Y : T with Address => X'Address, Import, Alignment => Integer'Alignment;

   procedure Swap (A, B : out T) with Pre => True is
   begin
      A.C := 11111;
      B.C := 22222;
      pragma Assert (A.C = 11111);
   end;

   procedure Swap (A : out T) with Pre => True, Global => (Output => X) is
   begin
      A.C := 11111;
      X.C := 22222;
      pragma Assert (A.C = 11111);
   end;

begin
   Swap (Y);
   Swap (X, Y);
   Swap (Y, X);
end;
