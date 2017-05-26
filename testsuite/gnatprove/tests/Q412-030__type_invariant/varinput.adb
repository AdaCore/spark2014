package body Varinput is

   function Func_Visible return Boolean is
   begin
      return True;
   end;

   function Func return Boolean is
   begin
      return True;
   end;

   function Instance_Func is new Func (F2);

end Varinput;
