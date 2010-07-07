package body P is

   function Proc return Integer is
      
      function Zero return Integer is
      begin
	 return 0;
      end;
      
      X : Integer;
      
   begin
      
      X := Zero;
      return X;
      
   end;

end;
