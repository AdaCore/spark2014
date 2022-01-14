procedure Complex_Elsif (X : Boolean) with
   SPARK_Mode
is
   function F return Boolean is
      Dummy : constant Integer := 0;
   begin
      return True;
   end;
begin
   if X then
      null;
   elsif F then -- inlining-for-proof would expand F body into ELSIF actions
      null;
   end if;
end;
