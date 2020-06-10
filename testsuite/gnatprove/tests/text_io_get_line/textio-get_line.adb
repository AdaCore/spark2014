pragma SPARK_Mode;
pragma Unevaluated_Use_Of_Old (Allow);

with System;                  use System;
with System.Storage_Elements; use System.Storage_Elements;

separate (TextIO)
procedure Get_Line
  (File : in out File_Type;
   Item : out String;
   Last : out Natural)
is
   Cur_Position_At_Start : constant Positive := Cur_Position with Ghost;
   EOF_At_Start : constant Boolean := End_Of_File (File) with Ghost;

   Chunk_Size : constant := 80;
   --  We read into a fixed size auxiliary buffer. Because this buffer
   --  needs to be pre-initialized, there is a trade-off between size and
   --  speed. Experiments find returns are diminishing after 50 and this
   --  size allows most lines to be processed with a single read.

   ch : int;
   N  : Natural;

   procedure Get_Chunk (N : Positive; Rest : out Natural) with
     Pre  => N <= Chunk_Size and then
       Last in Item'First - 1 .. Item'Last and then
       (if N > 1 then Last + 1 >= Item'First and Last + N - 1 <= Item'Last) and then
       (if End_Of_File (File) then Last >= Item'First) and then
       --  Arbitrary bounding of Cur_Position model to avoid overflows
       Cur_Position <= 10_000,
     Post =>
       --  Slice of Item up to Last is untouched
       (for all Idx in Item'First .. Last'Old => Item (Idx) = Item'Old (Idx)) and then
       (Cur_Position - Cur_Position'Old = Last - Last'Old) and then

       --  Redundant postcondition for automatic proof
       (for all Idx in Last'Old + 1 .. Last =>
          Item (Idx) = The_File (Idx - Last'Old - 1 + Cur_Position'Old)) and then

       (if N = 1 then
          Last = Last'Old and then
          Rest = 1

        elsif End_Of_File (File)'Old then
          Last = Last'Old and then
          Rest = 0

        elsif No_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2)
                and then
              No_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2)
        then
           Last = Last'Old + N - 1 and then
           (for all Idx in 1 .. N - 1 =>
              Item (Last'Old + Idx) = The_File (Cur_Position'Old + Idx - 1)) and then
           Rest = 1

        elsif No_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) then
            (declare
                 LF_Pos : constant Positive := Find_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2);
             begin
               Last = Last'Old + LF_Pos - Cur_Position'Old and then
                 (for all Idx in Cur_Position'Old .. LF_Pos - 1 =>
                        Item (Last'Old + Idx - Cur_Position'Old + 1) = The_File (Idx)) and then
                   Rest = 0)

        else
          (declare
               EOF_Pos : constant Positive := Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2);
           begin
             Last = Last'Old + Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old and then
               (for all Idx in Cur_Position'Old .. Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) - 1 =>
                      Item (Last'Old + Idx - Cur_Position'Old + 1) = The_File (Idx)) and then
                 Rest = 0));
   --  Reads at most N - 1 characters into Item (Last + 1 .. Item'Last),
   --  updating Last. Raises End_Error if nothing was read (End_Of_File).
   --  Returns number of characters still to read (either 0 or 1) in
   --  case of success.

   ---------------
   -- Get_Chunk --
   ---------------

   procedure Get_Chunk (N : Positive; Rest : out Natural) is
      Buf : String (1 .. Chunk_Size);
      P   : Natural;
      Success : Boolean;
      EOF_At_Start : constant Boolean := End_Of_File (File) with Ghost;
      Last_At_Start : constant Natural := Last with Ghost;
      Cur_Position_At_Start : constant Positive := Cur_Position with Ghost;
      Item_At_Start : constant String := Item;

   begin
      --  Dummy initialization for proof
      Buf := (others => ' ');

      if N = 1 then
         Rest := N;
         return;
      end if;

      Memset (Buf, Character'Val (LM), N);

      pragma Assert (Buf (N) = ASCII.LF);

      Fgets(Buf, N, File.Descr, Success);

      if not Success then
         if ferror (File.Descr) /= 0 then
            raise Device_Error;
            pragma Annotate (GNATprove, Intentional, "exception might be raised", "system call might fail");

         --  If incomplete last line, pretend we found a LM

         elsif Last >= Item'First then
            Rest := 0;
            return;

         else
            raise End_Error;
         end if;
      end if;

      P := Memchr (Buf, ASCII.LF, N);

      --  If no LM is found, the buffer got filled without reading a new
      --  line. Otherwise, the LM is either one from the input, or else one
      --  from the initialization, which means an incomplete end-of-line was
      --  encountered. Only in first case the LM will be followed by a 0.

      if P = 0 then
         Memcpy (S1 => Item, From1 => Last + 1,
                 S2 => Buf, From2 => 1, N => N - 1);
         Last := Last - 1 + N;

         Rest := 1;

         return;

      else
         --  P points to the LM character. Set K so Buf (K) is the character
         --  right before.

         declare
            K : Natural := Natural (P - 1);

         begin
            --  Now Buf (K + 2) should be 0, or otherwise Buf (K) is the 0
            --  put in by fgets, so compensate.

            pragma Assert (if No_Char_In_Slice (EOF_Ch, Cur_Position_At_Start, Cur_Position_At_Start + N - 2) then
                              K = Find_Char_In_Slice (ASCII.LF, Cur_Position_At_Start, Cur_Position_At_Start + N - 2) - Cur_Position_At_Start);

            if K + 2 > N or else Buf (K + 2) /= ASCII.NUL then

               --  Incomplete last line, so remove the extra 0

               pragma Assert (Buf (K) = ASCII.NUL);
               K := K - 1;
            end if;

            Memcpy (S1 => Item, From1 => Last + 1,
                    S2 => Buf, From2 => 1, N => K);
            Last := Last + K;

         end;

         Rest := 0;
         return;
      end if;
   end Get_Chunk;

   Rest : Integer;

--  Start of processing for Get_Line

begin
   --  Dummy initializations for proof
   Item := (others => ' ');
   Last := Item'First - 1;

   --  Immediate exit for null string, this is a case in which we do not
   --  need to test for end of file and we do not skip a line mark under
   --  any circumstances.

   if Item'First > Item'Last then
      return;
   end if;

   N := Item'Last - Item'First + 1;

   while N >= Chunk_Size loop
      pragma Loop_Invariant (Last + 1 >= Item'First and then
                             Last + N = Item'Last);
      pragma Loop_Invariant (for all Idx in Item'First .. Last =>
                               Item (Idx) = The_File (Idx - Item'First + Cur_Position'Loop_Entry));
      pragma Loop_Invariant (Cur_Position = Cur_Position'Loop_Entry + Last - Item'First + 1);

      --  Arbitrary bounding of Cur_Position model to avoid overflows
      pragma Assume (Cur_Position <= 10_000);
      Get_Chunk (Chunk_Size, Rest);

      if Rest = 0 then
         N := 0;
      else
         N := N - Chunk_Size + 1;
      end if;

   end loop;

   if N > 1 then
      --  Arbitrary bounding of Cur_Position model to avoid overflows
      pragma Assume (Cur_Position <= 10_000);
      Get_Chunk (N, Rest);
      N := Rest;
   end if;

   --  Almost there, only a little bit more to read

   if N = 1 then
      pragma Assert (Last + N = Item'Last);
      Getc (File, Ch);

      --  If we get EOF after already reading data, this is an incomplete
      --  last line, in which case no End_Error should be raised.

      if Ch = EOF then
         if  Last < Item'First then
            raise End_Error;

         else  --  All done
            return;
         end if;

      elsif Ch /= LM then

         --  Buffer really is full without having seen LM, update col

         Last := Last + 1;
         Item (Last) := Character'Val (Ch);
         return;
      end if;
   end if;

end Get_Line;
