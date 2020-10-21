procedure Fibo_Variant with SPARK_Mode is
   function Fibo (N : Natural) return Natural with
     Subprogram_Variant => (Decreases => Z + 1, Increases => -N, Decreases => Z); --@OVERFLOW_CHECK:FAIL
   Z : Integer;

   function Fibo (N : Natural) return Natural is
   begin
      if N < 3 then
         return 1;
      else
         return Fibo (N - 1) --@SUBPROGRAM_VARIANT:PASS
           + Fibo (N - 2); --@SUBPROGRAM_VARIANT:PASS @OVERFLOW_CHECK:FAIL
      end if;
   end Fibo;

begin
   null;
end;
