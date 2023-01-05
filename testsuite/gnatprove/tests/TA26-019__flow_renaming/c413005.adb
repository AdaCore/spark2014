with C413005P;
procedure C413005 is

   generic
      with function Get return Integer;
      with procedure Set (Value : in Integer);
   procedure Check;

   procedure Check is
   begin
      Set (1);
      if Get /= 0 then
         raise Program_Error;
      end if;
   end Check;

   function Func return access C413005P.TP is
   begin
      return null;
   end Func;

   Obj1 : C413005P.TP;
   Obj2 : C413005P.TP;

   procedure Check1 is new Check (Obj1.Class_Wide_Get, Obj1.Class_Wide_Set);
   procedure Check2 is new Check (Obj2.Get, Obj2.Set);
   procedure Check3 is new Check (Func.Class_Wide_Get, Func.Class_Wide_Set);

begin
   null;
end C413005;
