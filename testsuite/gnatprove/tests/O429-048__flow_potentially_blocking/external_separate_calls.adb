package body External_Separate_Calls is

   protected body PT is
      entry Enter when True is
      begin
         Divert_Control_From_PO1_To_PO2;
      end;

      procedure Reenter is
      begin
         null;
      end;
   end;

   --  second PT instance
   PO2 : PT;

   procedure Divert_Control_From_PO1_To_PO2 is
   begin
      PO2.Reenter;
   end;

end;
