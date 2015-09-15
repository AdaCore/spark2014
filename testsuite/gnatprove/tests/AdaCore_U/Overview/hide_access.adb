package body Hide_Access with SPARK_Mode => Off is

   procedure Store (D : in out Dictionary; W : String) is -- with SPARK_Mode => On is
      First_Letter : constant Letter := W (W'First);
   begin
      D (First_Letter) := New_String_Access (W);
   end Store;
end Hide_Access;
