procedure P is
   type Bool_Int is mod 2;

   type To_Int_Map is array (Boolean) of Bool_Int;

   To_Int : To_Int_Map;
   Val    : Bool_Int := 0;
begin
   for B in Boolean'Range loop
      To_Int (B) := Val;
      Val := Val + 1;
   end loop;
end P;
