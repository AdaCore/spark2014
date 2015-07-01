package body P is

   protected body Empty is
      entry Dummy when True is
      begin
         null;
      end Dummy;
   end Empty;

end P;
