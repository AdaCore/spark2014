with State;

procedure Pure_Procedure (X : in out Integer) is
begin
   X := X + State.Y;
end Pure_Procedure;
