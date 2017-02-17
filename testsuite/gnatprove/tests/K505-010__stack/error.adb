package body Error is

   function Get_Current return State is
   begin
      return MyState;
   end;

   procedure Set_Erroneous is
   begin
      MyState := Erroneous;
   end;

   procedure Reset is
   begin
      MyState := Normal;
   end;

end Error;
