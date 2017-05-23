pragma SPARK_Mode;

with Test;

procedure Main
  with Post => True
is
   X : constant Integer := Test.Test with Ghost;
begin
   null;
end;
