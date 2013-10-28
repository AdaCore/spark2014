pragma SPARK_Mode;
procedure Init is
   generic
      L, U : Integer;
   package P is
      subtype Index is Integer range L .. U;
      type Arr is array (Index) of Index;
      function Get return Arr;
   end P;
   package body P is
      function Get return Arr is
         A : Arr;
      begin
         for I in Index loop
            A(I) := I + 1;
         end loop;
         return A;
      end Get;
   end P;
   package Inst is new P (1, 10);
begin
   null;
end Init;
