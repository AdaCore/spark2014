package Tasks is

   task type Timer
   is
      pragma Priority (10);
   end Timer;

   task type Timer_Stub;

   protected type Store
   is
      pragma Priority (10);
      function Get return Integer;
      procedure Put (X : in Integer);
      entry Wait;
   private
      The_Stored_Data : Integer := 0;
      The_Guard : Boolean := False;
   end Store;

   protected type Store_Stub
   is
      procedure Put (X : in Integer);
      entry Wait;
   private
      The_Stored_Data : Integer := 0;
   end Store_Stub;

end Tasks;
