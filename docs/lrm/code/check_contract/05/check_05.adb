package body Check_05
is
   procedure Compare(A, B : in Small; C : in out Big)
   is
   begin
      if (A + B >= C) then
	 C := A;
	 C := C + B;
	 C := C + 1;
      end if;
      --# check A + B < C;
   end Compare;
end Check_05;
