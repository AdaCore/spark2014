with Helpers; use Helpers;
with TextIO; use TextIO;

procedure Test_Get_Line is
   procedure Set_The_Line_With_EOF (S : String) is
   begin
      The_File (S'Range) := S;
      The_File (S'Last + 1 .. The_File'Last) := (others => EOF_Ch);
   end Set_The_Line_With_EOF;

   procedure Set_The_Line_With_LF (S : String) is
   begin
      The_File (S'Range) := S;
      The_File (S'Last + 1 .. The_File'Last) := (others => ASCII.LF);
   end Set_The_Line_With_LF;

   procedure Reset_The_Line is
   begin
      Cur_Position := 1;
   end Reset_The_Line;

begin
   declare
      S : constant String := "hello world!";
      Last : Natural;
   begin
      Set_The_Line_With_EOF (S);

      for Buf_Size in 0 .. S'Length loop
         declare
            Buf : String (1 .. Buf_Size);
         begin
            Reset_The_Line;
            Get_Line (Buf, Last);
            pragma Assert (Last = Buf'Last);
            pragma Assert (S (1 .. Last) = Buf);
         end;
      end loop;

      for Buf_Size in S'Length .. 100 loop
         declare
            Buf : String (1 .. Buf_Size);
         begin
            Reset_The_Line;
            Get_Line (Buf, Last);
            pragma Assert (Last = S'Last);
            pragma Assert (S = Buf (1 .. Last));
         end;
      end loop;
   end;

   declare
      S : constant String := "hello world!";
      Last : Natural;
   begin
      Set_The_Line_With_LF (S);

      for Buf_Size in 0 .. S'Length loop
         declare
            Buf : String (1 .. Buf_Size);
         begin
            Reset_The_Line;
            Get_Line (Buf, Last);
            pragma Assert (Last = Buf'Last);
            pragma Assert (S (1 .. Last) = Buf);
         end;
      end loop;

      for Buf_Size in S'Length .. 100 loop
         declare
            Buf : String (1 .. Buf_Size);
         begin
            Reset_The_Line;
            Get_Line (Buf, Last);
            pragma Assert (Last = S'Last);
            pragma Assert (S = Buf (1 .. Last));
         end;
      end loop;
   end;


end Test_Get_Line;
