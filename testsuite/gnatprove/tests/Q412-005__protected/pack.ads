package Pack is

   protected PO_Func is
      function Func return Boolean with Post => Func'Result = True;
      entry E_Func;
   end;

end Pack;
