procedure Multi is
   --  Type with mutable discriminant

   type U (D : Integer := 0) is record
      C : Integer;
   end record;

   --  Unconstrained objects

   X, Y, Z : U;

   --  Callee with symmetric unconstrained global outputs

   procedure Flow with Pre => True, Global => (Output => (X, Y, Z)) is
   begin
      X := (D => 0, C => 0);
      Y := (D => 0, C => 0);
      Z := (D => 0, C => 0);
   end;

   --  Caller with symmetric dependency clauses

   procedure Flow2 with Pre => True,
      Depends => (X => (X, Y, Z),
                  Y => (X, Y, Z),
                  Z => (X, Y, Z))
   is
   begin
      Flow;
   end;
begin
   null;
end;
