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
--        CC : constant A (0 .. My_Index'Last) := (others => False);
begin
   if C'Length > My_Index'Last then
      Ada.Text_IO.Put_Line ("max");
   elsif C'Length = My_Index'First then
      Ada.Text_IO.Put_Line ("zero");
   end if;
   if C (My_Index'Last) and C (0) then
      Ada.Text_IO.Put_Line ("???");
   end if;

   if C'Length > Long_Long_Integer'Last then
      Ada.Text_IO.Put_Line ("max");
   elsif C'Length = Long_Long_Integer (0) then
      Ada.Text_IO.Put_Line ("zero");
   end if;
   pragma Assert (C'Length /= Long_Long_Integer (0)); --@ASSERT:FAIL
end Fail;
