package P is
   generic
   procedure Proc;

   generic
   function Func return Integer;

   generic
   package Pack is
      procedure Dummy;
   end;
end;
