with System;                  use System;
with System.Storage_Elements; use System.Storage_Elements;

package body TextIO with
  SPARK_Mode,
  Refined_State => (Current_Input_File => Current_In)
is

   pragma Warnings (Off, "*unused initial value of constant with variable input ""EOF""*");
   procedure Getc (File : File_Type; Ch : out Int) with
     Global => (Input => (EOF, EOF_Ch, The_File), In_Out => Cur_Position),
     Post => (if The_File (Cur_Position'Old) = EOF_Ch then
                Cur_Position = Cur_Position'Old and then
                Ch = EOF
              elsif The_File (Cur_Position'Old) = ASCII.LF then
                Cur_Position = Cur_Position'Old and then
                Ch = LM
              else
                Cur_Position = Cur_Position'Old + 1 and then
                Ch = Character'Pos (The_File (Cur_Position'Old)));
   pragma Warnings (On, "*unused initial value of constant with variable input ""EOF""*");
   --  Gets next character from file, which has already been checked for being
   --  in read status, and returns the character read if no error occurs. The
   --  result is EOF if the end of file was read.

   ----------
   -- Getc --
   ----------

   procedure Getc (File : File_Type; Ch : out Int) is
   begin
      fgetc (File.Descr, ch);

      if ch = EOF and then ferror (File.Descr) /= 0 then
         raise Device_Error;
         pragma Annotate (GNATprove, Intentional, "exception might be raised", "system call might fail");
      end if;
   end Getc;

   procedure Memcpy
     (S1 : in out String;
      S2 : String;
      From1, From2 : Positive;
      N : Natural)
   with
     Pre =>
       (if N /= 0 then
          From1 in S1'Range and then
          From1 + N - 1 in S1'Range and then
          From2 in S2'Range and then
          From2 + N - 1 in S2'Range),
     Contract_Cases =>
       (N = 0  => S1 = S1'Old,
        N /= 0 => (for all Idx in S1'Range =>
                     (if Idx in From1 .. From1 + N - 1 then S1 (Idx) = S2 (Idx - From1 + From2)
                      else S1 (Idx) = S1'Old (Idx))));
   pragma Annotate (GNATprove, Terminating, Memcpy);
   procedure Memcpy
     (S1 : in out String;
      S2 : String;
      From1, From2 : Positive;
      N : Natural)
   is
      pragma SPARK_Mode (Off);
      procedure memcpy (s1, s2 : chars; n : size_t);
      pragma Import (C, memcpy);
   begin
      memcpy (S1 (From1)'Address, S2 (From2)'Address, size_t (N));
   end Memcpy;

   function Memchr
     (S  : String;
      Ch : Character;
      N  : Natural) return Natural
   with
     Pre  => N <= S'Length,
     Post => (if Has_Char_In_String (S, Ch, N) then
                Memchr'Result = Find_Char_In_String (S, Ch, N)
              else
                Memchr'Result = 0);
   pragma Annotate (GNATprove, Terminating, Memchr);
   function Memchr
     (S  : String;
      Ch : Character;
      N  : Natural) return Natural
   is
      pragma SPARK_Mode (Off);
      function memchr (s : chars; ch : int; n : size_t) return chars;
      pragma Import (C, memchr);

      P : chars;
   begin
      P := memchr (S (S'First)'Address, LM, size_t (N));
      if P = Null_Address then
         return 0;
      else
         return S'First + Natural (P - S (S'First)'Address);
      end if;
   end Memchr;

   procedure Memset
     (B  : in out String;
      Ch : Character;
      N  : Natural)
   with
     Pre  => N <= B'Length,
     Post => (for all Idx in B'Range =>
                (if Idx < B'First + N then B (Idx) = Ch else B (Idx) = B'Old (Idx)));
   pragma Annotate (GNATprove, Terminating, Memset);
   procedure Memset
     (B  : in out String;
      Ch : Character;
      N  : Natural)
   is
      pragma SPARK_Mode (Off);
      procedure memset (b : chars; ch : int; n : size_t);
      pragma Import (C, memset);
   begin
      memset (B (B'First)'Address, Character'Pos (Ch), size_t (N));
   end Memset;

   --------------
   -- Get_Line --
   --------------

   procedure Get_Line
     (File : in out File_Type;
      Item : out String;
      Last : out Natural) is separate;
   --  The implementation of Ada.Text_IO.Get_Line is split into a subunit so
   --  that different implementations can be used on different systems.

   procedure Get_Line
     (Item : out String;
      Last : out Natural)
   is
   begin
      Get_Line (Current_In, Item, Last);
   end Get_Line;

   procedure Get_Line_Function (File : in out File_Type; Result : out String; Num : out Natural) is

      Cur_Position_At_Start : constant Positive := Cur_Position with Ghost;

      procedure Get_Rest (S : String; Result : out String; Num : out Natural) with
        Global => (Input => (EOF, EOF_Ch, Cur_Position_At_Start), In_Out => (File, The_File, Cur_Position)),
        Pre  => not End_Of_File (File) and then
                Result'First = 1 and then
                Result'Last = Positive'Last and then
                Cur_Position = Cur_Position_At_Start + S'Last - S'First + 1 and then
                (for all Idx in S'Range =>
                   S (Idx) = The_File (Idx - S'First + Cur_Position_At_Start)),
        Post =>
             (for all Idx in 1 .. Num =>
                Result (Idx) = The_File (Idx - 1 + Cur_Position_At_Start)) and then
             Cur_Position = Cur_Position_At_Start + Num and then
             (The_File (Cur_Position) = EOF_Ch or else
              The_File (Cur_Position) = ASCII.LF);

      --  This is a recursive function that reads the rest of the line and
      --  returns it. S is the part read so far.

      --------------
      -- Get_Rest --
      --------------

      procedure Get_Rest (S : String; Result : out String; Num : out Natural) is

         --  The first time we allocate a buffer of size 500. Each following
         --  time we allocate a buffer the same size as what we have read so
         --  far. This limits us to a logarithmic number of calls to Get_Rest
         --  and also ensures only a linear use of stack space.

         Buffer : String (1 .. Integer'Max (500, S'Length));
         Last   : Natural;

      begin
         Get_Line (File, Buffer, Last);

         declare
            R : constant String := S & Buffer (1 .. Last);
         begin
            pragma Assert (R'First = S'First);
            pragma Assert (R'Last = S'Last + Last);

            Num := S'Last - S'First + 1 + Last;

            if Last < Buffer'Last then
               Result (1 .. Num) := R;

            else
               pragma Assert (Last = Buffer'Last);

               --  If the String has the same length as the buffer, and there
               --  is no end of line, check whether we are at the end of file,
               --  in which case we have the full String in the buffer.

               if End_Of_File (File) then
                  Result (1 .. Num) := R;

               else
                  Get_Rest (R, Result, Num);
               end if;
            end if;
         end;
      end Get_Rest;

   --  Start of processing for Get_Line

   begin
      Get_Rest ("", Result, Num);
   end Get_Line_Function;

end TextIO;
