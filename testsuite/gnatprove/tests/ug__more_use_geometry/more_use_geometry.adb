with Geometry; use Geometry;

procedure More_Use_Geometry (S1, S2, S3, S4 : in out Shape'Class) with
  SPARK_Mode,
  Pre => S1.Valid
is
begin
   S1.Operate;

   if S2.Valid then
      S2.Operate;
   end if;

   S3.Set_Default;
   S3.Operate;

   S4.Operate;
end More_Use_Geometry;
