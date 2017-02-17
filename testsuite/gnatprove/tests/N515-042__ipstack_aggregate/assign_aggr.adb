package body Assign_Aggr is

   procedure Consume (U : T; Err : out Boolean) is
   begin
      if U.X > U.Y then
         Err := True;
      else
         Err := False;
      end if;
   end Consume;

   procedure Compute (V : out Integer) is
      Err : Boolean;
      W : T;
   begin
      W := (0, 0, 0);
      Consume (W, Err);
      V := 10;
   end Compute;

end Assign_Aggr;
