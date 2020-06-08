package body P is
   protected body PT is
      procedure Aborting with No_Return, Global => null is
      begin
         raise Program_Error;
      end;

      procedure Caller with Global => null is
      begin
         Aborting;
      end;
   end;
end;
