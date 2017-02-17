with Types; use Types;
with PrefixSum; use PrefixSum;
with Ada.Text_IO; use Ada.Text_IO;
procedure Main is pragma SPARK_Mode (On);

   procedure Print_Array (A : Input) is
   begin
      Put ("A = (");
      for J in A'Range loop
         Put (Integer'Image (A (J)));
      end loop;
      Put (" )");
      Put_Line ("");
   end Print_Array;

   A     : Input := (3, 1, 7, 0, 4, 1, 6, 3);
   Space : Positive;

   Copy  : Input := A;
begin
   Print_Array (A);

   Upsweep (A, Space);
   Put_Line ("L =" & Index'Image (Space));
   Print_Array (A);

   Downsweep (Copy, A, Space);
   Print_Array (A);
end Main;


