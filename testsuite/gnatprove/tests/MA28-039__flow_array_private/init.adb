pragma SPARK_Mode;
procedure Init is
   package P is
      subtype Index is Integer range 1 .. 10;
      type Arr is private;
      function Get return Arr;
   private
      type Arr is array (Index) of Index;
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
begin
   null;
end Init;
