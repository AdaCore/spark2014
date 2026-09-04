pragma Extensions_Allowed (All_Extensions);

procedure Test
  (B1, B2     : Boolean;
   X1, X2     : Integer;
   Y1, Y2     : Integer;
   Output     : out Long_Integer)
with
  SPARK_Mode,
  Depends => (Output => (B1, X1, Y1), null => (B2, X2, Y2))
is
   B : Boolean := B1;
   X : Integer := X1;
   Y : Integer := Y1;
begin
   <<Capture>>
   B := B2;
   X := X2;
   Y := Y2;
   Output := Long_Integer ((if B then X else Y))'At (Capture);
end Test;
