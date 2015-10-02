package body Attach_Test is

   protected body Prot is
      procedure Start is
      begin
         A := 1;
      end Start;

      procedure Stop is
      begin
         A := 0;
      end Stop;
   end Prot;

end Attach_Test;
