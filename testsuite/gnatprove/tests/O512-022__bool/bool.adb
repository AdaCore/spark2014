procedure Bool is pragma SPARK_Mode (On);
   --  in place swapping of Boolean values
   procedure Swap (X, Y : in out Boolean) with
     Post => X = Y'Old and Y = X'Old
   is
   begin
      X := X xor Y;
      Y := X = Y;    --  Y is not X'Old
      X := X xor Y;  --  X is not Y'Old
      X := not X;    --  X is Y'Old
      Y := not Y;    --  Y is X'Old
   end Swap;

   procedure Implies (X, Y : in out Boolean) with
     Post => X = (X'Old <= Y'Old)
       and then Y = (Y'Old <= X'Old)
       and then ((X'Old = Y'Old) <= (X = Y))
       and then ((X'Old = Y'Old) = (X = Y));

   procedure Implies (X, Y : in out Boolean) is
      Z : constant Boolean := X and Y;
   begin
      X := not X or Z;
      Y := not Y or Z;
   end Implies;

   X, Y : Boolean;
begin
   X := True;  Y := False; Swap (X, Y); Implies (X, Y);
   X := False; Y := True;  Swap (X, Y); Implies (X, Y);
   X := False; Y := False; Swap (X, Y); Implies (X, Y);
   X := True;  Y := True;  Swap (X, Y); Implies (X, Y);
end Bool;
