package External_Separate_Calls is

   protected type PT is
      entry Enter;       -- entry point
      procedure Reenter; -- reentry point;
   end;

   --  first PT instance
   PO1 : PT;

   --  external procedure that switches control from PO1 to PO2
   procedure Divert_Control_From_PO1_To_PO2;

end;
