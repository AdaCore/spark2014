with H;
with H_3;

procedure Test with SPARK_Mode is
   X : H.Child := H.Create;            --  Should be accepted
   Y : H_3.Grand_Child := H_3.Create;  --  Should be accepted

begin
  null;
end Test;
