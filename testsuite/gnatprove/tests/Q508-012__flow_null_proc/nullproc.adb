package body Nullproc is

   protected body Protected_Type is
      procedure Dummy is
         procedure Test_Protected_Type
         with Depends => (null => Protected_Type)
         is begin null; end;
      begin
         null;
      end;
   end;

   task body Single_Task_Type is
   begin
      null;
   end;

end;
