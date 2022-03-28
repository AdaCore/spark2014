package body Case_Stmt is

  ----------------
  -- Int_Range --
  ----------------

  procedure Index_Range (I : Index) is
    A : Action;
  begin
    case I is
      when 10 .. 18 => A := Work;  pragma Assert (A = Nothing); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when 19 .. 20 => A := Party; pragma Assert (A = Nothing); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when others   => A := Sleep; pragma Assert (A = Nothing); -- @ASSERT:FAIL @COUNTEREXAMPLE
    end case;
  end Index_Range;

  -----------------
  -- Int_Subtype --
  -----------------

  procedure Index_Subtype (K : Index) is
    J : Index;
  begin
    case K is
      when Ten_Fourteen    => J := 1; pragma Assert (J /= 1); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when Fifteen_Twenty  => J := 2; pragma Assert (J /= 2); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when Lower_Than_Five => J := 3; pragma Assert (J /= 3); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when Five_To_Nine    => J := 4; pragma Assert (J /= 4); -- @ASSERT:FAIL @COUNTEREXAMPLE
    end case;
  end Index_Subtype;

  ----------------
  -- Week_Range --
  ----------------

  procedure Week_Range (D : Day) is
    A : Action;
  begin
    case D is
      when Mon .. Thu => A := Work;  pragma Assert (A = Nothing); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when Fri        => A := Party; pragma Assert (A = Nothing); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when Sat .. Sun => A := Sleep; pragma Assert (A = Nothing); -- @ASSERT:FAIL @COUNTEREXAMPLE
    end case;
  end Week_Range;

  -----------------------------------
  -- Week_Static_Disrete_Predicate --
  -----------------------------------

  procedure Week_Static_Predicate (D : Day) is
    A : Action;
  begin
    case D is
      when Weekend   => A := Sleep; pragma Assert (A /= Sleep); -- @ASSERT:FAIL @COUNTEREXAMPLE
      when Wednesday => A := Work;  pragma Assert (A /= Work);  -- @ASSERT:FAIL @COUNTEREXAMPLE
      when others    => A := Work;  pragma Assert (A /= Work);  -- @ASSERT:FAIL @COUNTEREXAMPLE
    end case;
  end Week_Static_Predicate;

end Case_Stmt;
