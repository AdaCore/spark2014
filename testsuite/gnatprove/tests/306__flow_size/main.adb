with Ada.Text_IO; use Ada.Text_IO;
with Full;

procedure Main is
   procedure Test (A, B : Integer) is
      Y1, Y2, Y3, Y4, Y5 : Natural;
      Z1, Z2, Z3 : Boolean;
   begin
      Full (A, B,  Y1, Y2, Y3, Y4, Y5, Z1, Z2, Z3);
      Put_Line (Integer'Image (Y1));
      Put_Line (Integer'Image (Y2));
      Put_Line (Integer'Image (Y3));
      Put_Line (Integer'Image (Y4));
      Put_Line (Integer'Image (Y5));
      New_Line;
   end;
   function F return Integer is (0);
   S : String := "abc";
begin
   Test (1, 0);
   Test (1, 1);
   Test (1, 10);
   --  Depending on the low and high bounds passed via routine Test to Full,
   --  the output for x86_64 Linux shows that 'Size depends on the bounds:
   --   0
   --   0
   --   64
   --   64
   --   32
   --
   --   8
   --   32
   --   128
   --   128
   --   32
   --
   --   80
   --   320
   --   480
   --   480
   --   32
   Put_Line (Integer'Image (S (1 .. 1)'Size));
end;
