package body P is
   function Empty_Set return Set_Type is
   begin
      return 0;
   end;

   procedure Include (S : in out Set_Type; N : in Integer) is
   begin
      S := S + Set_Type (N);
   end;
end;
