with Mod_Array; use Mod_Array;
with Ada.Text_IO;
procedure Fail with SPARK_Mode is
   function Create (Last : My_Index) return A with
     Post => Create'Result'Last = Last and Create'Result'First = 0
   is
      R : A (0 .. Last) := (others => False);
   begin
      return R;
   end Create;

   C : constant A := Create (My_Index'Last);

   procedure P1 with Pre => C'First = 0 and C'Last = My_Index'Last
   is
   begin
      if C'Length > My_Index'Last then --@RANGE_CHECK:FAIL
         Ada.Text_IO.Put_Line ("max");
      elsif C'Length = My_Index'First then
         Ada.Text_IO.Put_Line ("zero");
      end if;
   end P1;

   procedure P2 with Pre => C'First = 0 and C'Last = My_Index'Last
   is
   begin
      if C (My_Index'Last) and C (0) then
         Ada.Text_IO.Put_Line ("???");
      end if;
   end P2;

   procedure P3 with Pre => C'First = 0 and C'Last = My_Index'Last
   is
   begin
      if C'Length > Long_Long_Integer'Last then --@RANGE_CHECK:FAIL
         Ada.Text_IO.Put_Line ("max");
      elsif C'Length = Long_Long_Integer (0) then
         Ada.Text_IO.Put_Line ("zero");
      end if;
   end P3;

   procedure P4 with Pre => C'First = 0 and C'Last = My_Index'Last
   is
   begin
      pragma Assert (C'Length /= Long_Long_Integer (0)); --@RANGE_CHECK:FAIL
   end P4;
begin
   P1;
   P2;
   P3;
   P4;
end Fail;
