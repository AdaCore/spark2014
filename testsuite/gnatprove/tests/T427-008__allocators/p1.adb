procedure P1 with SPARK_Mode is

  TYPE UA1 IS ARRAY (INTEGER RANGE <>) OF INTEGER with Default_Component_Value => 1;

  function Three return Integer is (3);
  function One return Integer is (1);

  SUBTYPE CA11 IS UA1 (One .. Three);

  TYPE A_UA11 IS ACCESS UA1 (2 .. 4);

   procedure T1 with Pre => True is
      V11 : A_UA11 := NEW CA11;  --@RANGE_CHECK:FAIL
   begin
      null;
   end T1;

   procedure T2 with Pre => True is
      W11 : A_UA11 := NEW CA11'(others => 0);  --@RANGE_CHECK:FAIL
   begin
      null;
   end T2;

begin
  null;
end;
