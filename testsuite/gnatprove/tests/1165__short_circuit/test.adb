pragma Ada_2022;
pragma Short_Circuit_And_Or;

procedure Test with SPARK_Mode is
   procedure P (X : Integer; B : out Boolean) is
   begin
      B := X /= 0 and 20 mod X = 0; --@DIVISION_CHECK:PASS
   end P;
begin
   null;
end;
