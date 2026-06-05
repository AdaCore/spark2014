procedure Flow1 is

   X : String (1 .. 3) := "abc";
   Y : Positive;
   Z : Boolean;

   procedure Maybe_Write with
     Global   => (In_Out => X, Proof_In => (Y, Z)),
     Depends  => (X => X),
     Modifies => (X (Y) when Z);

   procedure Maybe_Write is
   begin
      null;
   end;
begin
   Maybe_Write;
end;
