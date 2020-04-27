procedure P2 with SPARK_Mode is

  TYPE UA1 IS ARRAY (INTEGER RANGE <>) OF INTEGER with Default_Component_Value => 1;

  function Seven return Integer is begin return 7; end;

  SUBTYPE CA11 IS UA1 (2 .. Seven);

  TYPE A_UA11 IS ACCESS UA1 (2 .. 4);

  V11 : A_UA11 := NEW CA11;  --  CE (RM 4.8(10/2))

begin
  null;
end;
