with Effect;

procedure E with No_Return, Global => (In_Out => Effect.X) is
begin
   Effect.X := not Effect.X;

   --  implicit return violates the No_Return contract
end;
