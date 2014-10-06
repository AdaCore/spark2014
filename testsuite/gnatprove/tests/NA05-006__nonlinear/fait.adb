procedure Fait (I ,J : Integer; R, K, Q : out Integer) with
  SPARK_Mode,
  Pre  => I >= -10 and I <= -1 and J >= 1 and J <= 10,
  Post => Q >= -99 and Q <= -J is
begin
   R:=I*J;
   K:=R+1;
   Q:=K;
end Fait;
