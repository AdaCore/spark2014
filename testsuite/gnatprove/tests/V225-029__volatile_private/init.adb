package body Init is

   procedure Initialize (Shared_Context : out Shared_Context_Type) is
   begin
      if True then  --  dummy condition to hide recursion from GNAT
         Initialize (Shared_Context);
      end if;
   end Initialize;

end Init;
