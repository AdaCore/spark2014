
procedure Test_Dispatch with SPARK_Mode is
   package Nested is
      type Root is tagged record
         F : Integer;
      end record;

      function Get_F (R : Root) return Integer is (R.F);
   end Nested;
   use Nested;

   procedure Use_Get_F_1 (RC : Root'Class) with
     Global => null,
     Pre => RC.F = 23 and then RC in Root
   is
   begin
      pragma Assert (Get_F (RC) = 23); -- @ASSERT:PASS
   end Use_Get_F_1;

   procedure Use_Get_F_2 (RC : Root'Class) with
     Global => null,
     Pre => RC.F = 23 and then RC in Root
   is
      C  : Integer := Get_F (RC);
   begin
      pragma Assert (C = 23); -- @ASSERT:PASS
   end Use_Get_F_2;

   procedure Use_Get_F_3 (RC : Root'Class) with
     Global => null,
     Pre => RC.F = 23 and then RC in Root
   is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Get_F);
   begin
      pragma Assert (Get_F (RC) = 23); -- @ASSERT:FAIL
   end Use_Get_F_3;

   procedure Use_Get_F_4 (RC : Root'Class) with
     Global => null,
     Pre => RC.F = 23 and then RC in Root
   is
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Get_F);
      C  : Integer := Get_F (RC);
   begin
      pragma Assert (C = 23); -- @ASSERT:FAIL
   end Use_Get_F_4;
begin
   null;
end Test_Dispatch;
