package body Attach_Test is

   protected body Prot is
      procedure Intr is
      begin
         A := Uninit; -- spontaneous read of an uninitialized data
      end;
   end;

end Attach_Test;
