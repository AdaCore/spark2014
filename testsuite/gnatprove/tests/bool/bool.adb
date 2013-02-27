procedure Bool is
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

   X, Y : Boolean;
begin
   X := True;  Y := False; Swap (X, Y);
   X := False; Y := True;  Swap (X, Y);
   X := False; Y := False; Swap (X, Y);
   X := True;  Y := True;  Swap (X, Y);
end Bool;
