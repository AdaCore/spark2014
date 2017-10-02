with System.Dim.Mks; use System.Dim.Mks;

procedure Use_Dims with SPARK_Mode is
   X : Speed := 0.0*m*s**(-1);
begin
   if X = 0.0*m*s**(-1) then
      return;
   end if;
end Use_Dims;
