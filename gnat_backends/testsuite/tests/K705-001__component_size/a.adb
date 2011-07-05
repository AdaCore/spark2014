package body A
is
   function Test return Boolean
   is
   begin
      return
         Data_Type'Size / Data_Type (8) = Data_Type (4) and
         Array_Type'Component_Size / Data_Type(8) = Data_Type(4);
   end Test;
end A;

