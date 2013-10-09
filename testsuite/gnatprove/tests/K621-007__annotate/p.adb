
package body P is
   pragma SPARK_Mode (Off);  --  access type
   G : Ptr;
   procedure Proc is
   begin
      G.all := 0;
   end;
end;
