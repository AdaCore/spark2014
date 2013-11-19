package body Check_14
  with SPARK_Mode
is
   procedure Compare(A, B : in Small; C : in out Big) is
   begin
      if A + B >= C then
	 C := A;
	 C := C + B;
	 C := C + 1;
      end if;
      pragma Assert (A + B < C);
   end Compare;
end Check_14;
