procedure Main with SPARK_Mode is
   procedure Div (A : Integer) is
   begin
      raise Program_Error with Integer'Image (1 / A);  --@DIVISION_CHECK:FAIL
   exception
      when Program_Error =>
         null;
   end;
   function Div_2 (A : Integer) return Integer is
   begin
      return (if A = 0 then raise Program_Error with Integer'Image (1 / A)  --@DIVISION_CHECK:FAIL
	      else 1 / A);
   end;

begin
   null;
end Main;
