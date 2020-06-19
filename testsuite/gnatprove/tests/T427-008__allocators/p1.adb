procedure P1 with SPARK_Mode is

  TYPE UA1 IS ARRAY (INTEGER RANGE <>) OF INTEGER with Default_Component_Value => 1;

  SUBTYPE CA11 IS UA1 (1 .. 3);

  TYPE A_UA11 IS ACCESS UA1 (2 .. 4);

  V11 : A_UA11 := NEW CA11;  --  CE (RM 4.8(10/2))

begin
  null;
end;
