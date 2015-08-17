package Pack is

   protected PO_Proc is
      procedure Proc;
      entry E_Proc;
   end;

   protected PO_Func is
      function Func return Boolean;
      entry E_Func;
   end;

   procedure External_Call_To_Protected_Proc;
   procedure External_Call_To_Protected_Func;

   protected PO_Safe is
      function Func return Boolean;
      procedure Proc;
      entry E_Safe;
   end;

end Pack;
