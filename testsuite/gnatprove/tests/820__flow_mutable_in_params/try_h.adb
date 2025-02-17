with H; use H;

procedure Try_H with SPARK_Mode is
   X : T := New_T;
begin
   P2 (X, X);
end Try_H;
