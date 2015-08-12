package Tasks is

   task type Task_With_Invalid_Discriminant (Countdown : access Natural)
   is
      pragma Priority (10);
   end;

   task type Timer (Countdown : Natural)
   is
      pragma Priority (10);
   end;

   task type Timer_Stub;

   X : aliased Integer;

   protected type Bad_Store
   is
      pragma Priority (10);
      function Get return Integer;
      procedure Put (X : in Integer);
      entry Wait (Dummy : Integer);
   private
      No_Default_Value : Integer;
      Forbidden_Integer : access Integer := X'Access;
      The_Stored_Data : Integer := 0;
      The_Guard : Boolean := False;
   end;

   protected type Simple
   is
     entry Dummy;
   end;

   subtype Sub_Simple is Simple;
   subtype Sub_Timer is Timer (5);

   protected type Store_Stub
   is
      procedure Put (X : in Integer);
      entry Wait;
   private
      The_Stored_Data : Integer := 0;
   end;

   protected type Invalid_Protected_Stub
   is
      entry Wait;
      procedure Proc;
   private
      No_Default_Value : Integer;
   end;

   protected type Store_With_No_Initialization
   is
      entry Wait (Dummy : Integer);
   private
      No_Default_Value : Integer;
   end;

   protected type Null_Protected_Type is
   end;

   protected type Store_With_Mixed_Initialization
   is
      entry Wait (Dummy : Integer);
   private
      Default_Value : Integer := 0;
      No_Default_Value : Integer;
   end;

end;
