with P;

procedure Test (Max : Positive) with SPARK_Mode is
   package B is new P (Max);
begin
   null;
end Test;
