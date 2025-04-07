procedure Warn with SPARK_Mode is
  pragma Warnings(Off, "subprogram * has no effect");

  Z : constant Integer := 0;
  procedure P
    with Pre => Z /= 0;

  procedure P is
  begin
    null;
  end P;
begin
  null;
end Warn;
