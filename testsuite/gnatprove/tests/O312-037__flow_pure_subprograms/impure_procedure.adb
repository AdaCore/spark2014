with State;

procedure Impure_Procedure (X : in out Integer) is
begin
   X := X + State.Y;
end Impure_Procedure;
