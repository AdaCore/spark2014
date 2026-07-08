procedure Illegal_Extended_Returns with SPARK_Mode is

   type Int_Access is not null access Integer;

   --  On traversal functtions, we should have checks that we return a part
   --  of the traversed parameter.

   function Bad_Param (X : Integer; Y : Int_Access) return not null access constant Integer is
   begin
      return B : not null access constant Integer := Y do
         null;
      end return;
   end Bad_Param;

begin
   null;
end;
