with Gen;
procedure Main with SPARK_Mode is

    function Read_Pre (Buffer : Gen.Ar) return Boolean is (Buffer'Length >= 2);
    procedure My_Read (Buffer : Gen.Ar; X : out Integer) is
    begin
      X := Buffer (Buffer'Last);
    end My_Read;
  function U is new Gen.F (My_Read, Read_Pre);
  Z : Integer := U;
begin
  null;
end Main;
