--  Derived from ACATS C48009A

procedure P3 with SPARK_Mode is
  type My_Int is new Integer with Default_Value => 3;

  SUBTYPE T1_7 IS My_Int RANGE 1..7;

  SUBTYPE T2_6 IS My_Int RANGE 2..6;

  TYPE AT1_7 IS ACCESS My_Int RANGE 1..7;

  TYPE AT2_6 IS ACCESS My_Int RANGE 2..6;

  function Seven return My_Int is begin return 7; end;

  VAT2_6 : AT2_6 := NEW T1_7;          -- OK (RM 4.8(9/2))

  VAT1_7 : AT1_7 := NEW T2_6'(Seven);  -- CE (RM 4.7(4))

begin
  null;
end;
