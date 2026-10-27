procedure Relaxed_Parts with SPARK_Mode is
   type RT is record
      X : Integer;
   end record
   with Relaxed_Initialization;

   type Container;
   type Access_T is access Container;

   type Container is record
      Data : RT;
      Next : Access_T;
   end record;

   type Wrapper is record
      Value : Access_T;
   end record;

   procedure Check (N : in out Access_T; Wrapped : out Wrapper)
   with Pre => N /= null,
        Relaxed_Initialization => Wrapped
   is
   begin
      Wrapped.Value := N;
      N := null;
      pragma Assert (Wrapped.Value /= null); -- @ASSERT:PASS
      pragma Assert (Wrapped.Value.all.Data'Initialized); -- @ASSERT:FAIL
   end Check;
begin
   null;
end Relaxed_Parts;
