package body Total is

   function Compute
     (In_Ctxt : in Enum)
      return Natural
   is
      My_Tot : Natural := 0;
   begin
      for Data in Enum loop
         if In_Ctxt = Ctxt (Data) then
            null;
         end if;
      end loop;
      return My_Tot;
   end Compute;

end Total;
