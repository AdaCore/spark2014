procedure Split_Pointer_Init with SPARK_Mode is
   type Ptr is access constant Integer;
   Value : aliased constant Integer := 42;
   P : Ptr with Relaxed_Initialization;

   function Ready return Boolean is (P'Initialized) with Ghost;
   function Is_Null return Boolean is (P = null) with
     Ghost,
     Pre => Ready;
   function Get return Integer is (P.all) with
     Ghost,
     Pre => Ready and then not Is_Null;

   --  Omitting the initialization precondition must leave a failed check.
   function Unguarded_Is_Null return Boolean is (P = null) with --@INIT_BY_PROOF:FAIL
     Ghost;
begin
   pragma Assert (Ready);
   pragma Assert (Is_Null);
   pragma Assert (Unguarded_Is_Null);
   P := Value'Access;
   pragma Assert (Ready);
   pragma Assert (not Is_Null);
   pragma Assert (Get = 42);
   --  The logic function must use the new pointer value.
   pragma Assert (Is_Null); --@ASSERT:FAIL
end Split_Pointer_Init;
