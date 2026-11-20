package body P is
   protected body Protected_Type is
      procedure Touch is
      begin
         Value := Value + 1;
      end Touch;
   end Protected_Type;
end P;
