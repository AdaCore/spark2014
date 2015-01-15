pragma Source_Reference (10, "master_file.adb");

procedure Not_This_Unit (X : in out Integer) with
  SPARK_Mode
is
begin
   X := X + 1;
end Not_This_Unit;
