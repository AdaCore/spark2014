procedure P is

   type Bool_Array is array (Boolean) of Integer;
   B : Bool_Array := (False .. True => 1);

begin
   null;
end P;
