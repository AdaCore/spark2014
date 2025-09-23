package body Prots is

   procedure P1 is
   begin
      PO.PP1;
   end;

   protected body PO_T is

      procedure PP1 is
      begin
         null;
      end;

   end PO_T;

   protected body Signal_Handler is

      procedure Teardown is
      begin
         P1;
      end;

   end Signal_Handler;

   protected body Signal2_Handler_Type is

      procedure Teardown is
      begin
         P1;
      end;

   end Signal2_Handler_Type;

begin
   null;

end Prots;
