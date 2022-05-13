procedure Main2 (W : Natural;
                 X : Natural;
                 Y : out Integer;
                 Z : out Integer) with
  Pre => X < Integer'Last,
  Depends => (Y => W, Z => X),
  Post => Y = W and Z = X + 1
  --  Contract is correct
is
   --  Multi-Layered discriminant dependency relations
   type T (D : Integer) is record
      C : Integer := D + 1;
   end record;

   type U (F : Integer := X) is record
      E : T (D => F);
   end record;

   G : U (F => W - 1);
   H : U;
begin
   Y := G.E.C;
   Z := H.E.C;
end;
