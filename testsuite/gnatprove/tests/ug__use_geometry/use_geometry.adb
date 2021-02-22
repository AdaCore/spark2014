with Geometry; use Geometry;

procedure Use_Geometry (S : in out Shape'Class) with
  SPARK_Mode
is
begin
   S.Set_Default;
   S.Operate;

   S.Set_Default_Repeat;
   S.Operate;

   S.Set_Default_No_Post;
   S.Operate;
end Use_Geometry;
