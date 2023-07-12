procedure Main2 with SPARK_Mode is
  function F return Integer with Post => True;
  function F return Integer is
  begin
    return 0;
  end F;

  X : Integer := F;
begin
  X := X + 1;
end Main2;
