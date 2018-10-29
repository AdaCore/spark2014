package body Repr with Spark_Mode is

  procedure P (A  : in out My_Arry;
                  B  : in My_Arry)
  is
        X : Uint64 := A'Length; --@RANGE_CHECK:PASS
        Z : Uint64 := B'Length / 16; --@RANGE_CHECK:PASS
        Temp_Buf    : My_Arry(A'First .. A'Last) := (others => 0);
  begin
     null;
  end P;

end Repr;
