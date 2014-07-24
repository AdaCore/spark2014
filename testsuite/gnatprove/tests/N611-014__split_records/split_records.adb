package body Split_Records with SPARK_Mode is
   procedure Update_Field_If_Possible
     (R : in out Record_With_Mutable_Discrs; New_Field : Natural)
   is
   begin
      if R.Present then
         R.Field := New_Field;
      elsif not R'Constrained then
         R := (Present => True, Field => New_Field);
      end if;
   end Update_Field_If_Possible;

   procedure Test is
      C1 : Record_With_Mutable_Discrs (False);
      C2 : Record_With_Mutable_Discrs := (Present => False);
      H1 : Holder (False);
      H2 : Mutable_Holder := (Content => (Present => False));
      A  : Mutable_Array (1 .. 1) := (1 => (Present => False));
      C3 : constant Record_With_Mutable_Discrs (False) := (Present => False);
      C4 : constant Record_With_Mutable_Discrs := (Present => False);
      H3 : constant Holder (False) := (Present => False,
                                       Content => (Present => False));
      H4 : constant Mutable_Holder := (Content => (Present => False));
      A2 : constant Mutable_Array (1 .. 1) := (1 => (Present => False));
   begin
      pragma Assert (C3'Constrained); --@ASSERT:PASS
      pragma Assert (C4'Constrained); --@ASSERT:PASS
      pragma Assert (H3.Content'Constrained); --@ASSERT:PASS
      pragma Assert (H4.Content'Constrained); --@ASSERT:PASS
      pragma Assert (A2 (1)'Constrained); --@ASSERT:PASS
      Update_Field_If_Possible (C1, 0);
      pragma Assert (not C1.Present);
      Update_Field_If_Possible (C2, 0);
      pragma Assert (not C2.Present); --@ASSERT:FAIL
      Update_Field_If_Possible (H1.Content, 0);
      pragma Assert (not H1.Content.Present);
      pragma Assert (not H2.Content'Constrained); --@ASSERT:PASS
      H2.Content := (Present => False);
      pragma Assert (not H2.Content'Constrained); --@ASSERT:PASS
      Update_Field_If_Possible (H2.Content, 0);
      pragma Assert (not H2.Content.Present); --@ASSERT:FAIL
      pragma Assert (not A (1)'Constrained); --@ASSERT:PASS
      A (1) := (Present => False);
      pragma Assert (not A (1)'Constrained); --@ASSERT:PASS
      Update_Field_If_Possible (A (1), 0);
      pragma Assert (not A (1).Present); --@ASSERT:FAIL
   end Test;
end;
