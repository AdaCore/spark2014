package body Assert_No_Loop_14
  with SPARK_Mode
is
   procedure Compare (A, B : in Small; C : in out Big) is
   begin
      if A + B >= C then
	 C := A;
	 C := C + B;
	 C := C + 1;
      end if;
      pragma Assert_And_Cut (A + B < C);
   end Compare;
end Assert_No_Loop_14;
