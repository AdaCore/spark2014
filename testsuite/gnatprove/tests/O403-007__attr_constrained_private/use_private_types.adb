package body Use_Private_Types with SPARK_Mode is

   procedure ReInit (S : in out P_Simple) is
   begin
      Private_ReInit (Simple (S)); --@PRECONDITION:FAIL
   end ReInit;
   procedure ReInit (S : in out Holder) is
   begin
      Private_ReInit (S.Content); --@PRECONDITION:PASS
   end ReInit;
   procedure ReInit (S : in out P_Holder) is
   begin
      Private_ReInit (Simple (S.Content));
   end ReInit;
   procedure ReInit (S : in out D_Holder_0) is
   begin
      pragma Assert (S.Content'Constrained); --@ASSERT:PASS
      Private_ReInit (Simple (S.Content)); --@PRECONDITION:PASS
   end ReInit;
   procedure ReInit (S : in out D_Holder_1) is
   begin
      Private_ReInit (Simple (S.Content)); --@PRECONDITION:FAIL
   end ReInit;

end Use_Private_Types;
