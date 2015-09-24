package body TP is
   task body Singl_Task is
   begin
      while B4 <= 10000 loop
         B4 := B4 + 1;
      end loop;
   end Singl_Task;

   protected body Singl_Prot is
      function Get_Content return Integer is
      begin
         if Give_Zero then
            return 0;
         elsif Give_One then
            return 1;
         else
            return Content;
         end if;
      end Get_Content;
   end Singl_Prot;
end TP;
