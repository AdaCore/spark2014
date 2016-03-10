package body Helpers is

   function Find_Char_In_Slice (Ch : Character; From, To : Positive) return Positive is
   begin
      for C in From .. To loop
         if The_File (C) = Ch then
            return C;
         end if;
      end loop;
      raise Program_Error;
   end Find_Char_In_Slice;

   function Find_Char_In_String (S : String; Ch : Character; N : Natural) return Positive is
   begin
      for C in S'First .. S'First - 1 + N loop
         if S (C) = Ch then
            return C;
         end if;
      end loop;
      raise Program_Error;
   end Find_Char_In_String;

   procedure Fgets
     (Strng   : in out String;
      N       : Natural;
      Stream  : File_Descr;
      Success : out Boolean)
   is
      Idx : Positive := 1;
      Cur : Character;
   begin
      Cur := The_File (Cur_Position);

      if Cur = EOF_Ch then
         Success := False;
         return;
      end if;

      for Local_Idx in 1 .. N - 1 loop
         Cur := The_File (Cur_Position);
         Idx := Local_Idx;
         exit when Cur = EOF_Ch;
         Strng (Idx) := Cur;
         exit when Cur = ASCII.LF;
         Cur_Position := Cur_Position + 1;
      end loop;

      if Cur = EOF_Ch then
         Strng (Idx) := ASCII.NUL;
      else
         Strng (Idx + 1) := ASCII.NUL;
      end if;

      Success := True;
   end Fgets;

   function ferror (stream : File_Descr) return Int is
   begin
      return 0;
   end Ferror;

   procedure fgetc (stream : File_Descr; result : out int) is
      C : constant Character := The_File (Cur_Position);
   begin
      if C = EOF_Ch then
         Result := EOF;
         return;
      end if;
      Result := Character'Pos (C);
      if C /= ASCII.LF then
         Cur_Position := Cur_Position + 1;
      end if;
   end Fgetc;

end Helpers;
