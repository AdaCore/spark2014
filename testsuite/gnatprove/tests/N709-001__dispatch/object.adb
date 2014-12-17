package body Object is

   procedure Set_Area (Obj : in out T; Value : Natural) is
   begin
      Obj.Area := Value;
   end Set_Area;

end Object;
