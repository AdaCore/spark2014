pragma Initialize_Scalars;

with Ada.Text_IO; use Ada.Text_IO;
with Full;

procedure Main is
   procedure Test (A, B : Integer) is
      Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8 : Natural;
   begin
      Full (A, B,  Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8);
      Put_Line (Integer'Image (Y1));
      Put_Line (Integer'Image (Y2));
      Put_Line (Integer'Image (Y3));
      Put_Line (Integer'Image (Y4));
      Put_Line (Integer'Image (Y5));
      New_Line;
   end;

   procedure Unsupported;
   --  unknown value of object alignment is rejected in marking

   procedure Unsupported with SPARK_Mode => Off is
      function F return Integer;
      --  function with I/O effect effect is rejected in marking

      function F return Integer with SPARK_Mode => Off is
      begin
         Ada.Text_IO.Put_Line ("F");
         return 0;
      end;

      S : String (1 .. 3);
      X : Natural;

   begin
      Put_Line (Integer'Image (F'Alignment));  --  F is evaluated
      Put_Line (Integer'Image (X'Alignment));  --  X is safe to be unintialized
      Put_Line (Integer'Image (S (1 .. F)'Alignment));  --  F is evaluted
      Put_Line (Integer'Image (S (1 .. X)'Alignment));  --  X is read
   end;

begin
   Test (1, 0);
   Test (1, 1);
   Test (1, 10);
   --  With different low and high bounds passed via routine Test to Full,
   --  the output for x86_64 Linux shows that 'Alignment does not depend on the
   --  bounds:
   --
   -- 1
   -- 4
   -- 4
   -- 4
   -- 4
   --
   -- 1
   -- 4
   -- 4
   -- 4
   -- 4
   --
   -- 1
   -- 4
   -- 4
   -- 4
   -- 4

end;
