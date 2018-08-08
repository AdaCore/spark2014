with System.Dim.Long_Mks; use System.Dim.Long_Mks;

procedure Use_Dims with SPARK_Mode is
   X : Speed := 0.0*m*s**(-1);
begin
   if X = 0.0*m*s**(-1) then
      return;
   end if;
end Use_Dims;
