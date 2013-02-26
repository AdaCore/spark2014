procedure Bool is
   --  in place swapping of Boolean values
   procedure Swap (X, Y : in out Boolean) with
     Post => X = not Y'Old and Y = not X'Old
   is
   begin
      X := X xor Y;
      Y := X = Y;  --  Y is not X'Old
      X := X xor Y;  --  X is not Y'Old
   end Swap;

   X, Y : Boolean;
begin
   X := True; Y := False; Swap (X, Y); Swap (X, Y);
   X := False; Y := False; Swap (X, Y);
   X := True; Y := True; Swap (X, Y);
end Bool;
