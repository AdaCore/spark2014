with Gen;

procedure Main with SPARK_Mode is
  function U is new Gen.F (100);
  procedure Test is
  begin
    pragma Assert (U = 100);
  end Test;
begin
  null;
end Main;
