with Interfaces.C_Streams;    use Interfaces.C_Streams;

package Helpers with SPARK_Mode is
   type File_Descr is private;

#if TEST_GET_LINE
   Huge         : constant := 100_000;
   The_File     : String (1 .. Huge);
   Cur_Position : Positive := 1;
#else
   The_File     : String (Positive) with Ghost;
   Cur_Position : Positive := 1 with Ghost;
#end if;

   EOF_Ch : constant Character := Character'Val (EOF mod 256);

   function fpeek (stream : File_Descr) return Int is
     (if The_File (Cur_Position) = EOF_Ch then EOF else Character'Pos (The_File (Cur_Position)))
#if TEST_GET_LINE
   ;
#else
   with Ghost;
#end if;

   function No_Char_In_Slice (Ch : Character; From, To : Positive) return Boolean is
      (for all Idx in From .. To => The_File (Idx) /= Ch)
#if TEST_GET_LINE
   ;
#else
   with Ghost;
#end if;

   function Has_Char_In_Slice (Ch : Character; From, To : Positive) return Boolean is
      (for some Idx in From .. To => The_File (Idx) = Ch)
#if TEST_GET_LINE
   ;
#else
   with Ghost;
#end if;

   function Find_Char_In_Slice (Ch : Character; From, To : Positive) return Positive with
      Ghost,
      Pre  => Has_Char_In_Slice (Ch, From, To),
      Post => Find_Char_In_Slice'Result in From .. To and then
              No_Char_In_Slice (Ch, From, Find_Char_In_Slice'Result - 1) and then
              The_File (Find_Char_In_Slice'Result) = Ch;

   function No_Char_In_String (S : String; Ch : Character; N : Natural) return Boolean is
      (for all Idx in S'First .. S'First - 1 + N => S (Idx) /= Ch)
   with
     Pre => S'First + N - 1 <= S'Last;

   function Has_Char_In_String (S : String; Ch : Character; N : Natural) return Boolean is
      (for some Idx in S'First .. S'First - 1 + N => S (Idx) = Ch)
   with
     Pre => S'First + N - 1 <= S'Last;

   function Find_Char_In_String (S : String; Ch : Character; N : Natural) return Positive with
      Ghost,
      Pre  => S'First + N - 1 <= S'Last and then Has_Char_In_String (S, Ch, N),
      Post => Find_Char_In_String'Result in S'First .. S'First - 1 + N and then
              No_Char_In_String (S, Ch, Find_Char_In_String'Result - 1) and then
              S (Find_Char_In_String'Result) = Ch;

   procedure Fgets
     (Strng   : in out String;
      N       : Natural;
      Stream  : File_Descr;
      Success : out Boolean)
   with
     Global => (Proof_In => (The_File, EOF), In_Out => Cur_Position, Input => EOF_Ch),
     Post => (if Success then

                --  Success means no error and no empty file

                (Ferror (Stream) = 0 and then Fpeek (Stream)'Old /= EOF) and then

                --  Case 1: no EOF nor newline character found

                --  N-1 characters are copied to Strng. Nul character is appended.
                --  Previous characters in Strng are preserved beyond the Nth character.
                --  Cur_Position advances N-1 characters.

                (if No_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2)
                      and then
                    No_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2)
                 then
                    Cur_Position = Cur_Position'Old + N - 1 and then
                    (for all Idx in 1 .. N - 1 =>
                       Strng (Idx) = The_File (Cur_Position'Old + Idx - 1)) and then
                    Strng (N) = ASCII.NUL and then
                    (for all Idx in N + 1 .. Strng'Last =>
                       Strng (Idx) = Strng'Old (Idx))

                 --  Case 2: newline character is found

                 --  Characters up to the newline are copied to Strng. Nul character is
                 --  appended. Previous characters in Strng are preserved beyond the nul
                 --  character. Cur_Position advances to the position of the newline
                 --  character.

                 elsif Has_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2)
                         and then
                       No_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2)
                 then
                    Cur_Position = Find_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2) and then
                    (for all Idx in Cur_Position'Old .. Find_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2) - 1 =>
                       Strng (Idx - Cur_Position'Old + 1) = The_File (Idx)) and then
                    Strng (Find_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old + 1) = ASCII.LF and then
                    Strng (Find_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old + 2) = ASCII.NUL and then
                    (for all Idx in Find_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old + 3 .. Strng'Last =>
                       Strng (Idx) = Strng'Old (Idx))

                 --  Case 3: EOF is found

                 --  Characters prior to EOF are copied to Strng. Nul character is
                 --  appended. Previous characters in Strng are preserved beyond the nul
                 --  character. Cur_Position advances to the position of EOF.

                 elsif No_Char_In_Slice (ASCII.LF, Cur_Position'Old, Cur_Position'Old + N - 2)
                         and then
                       Has_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2)
                 then
                    Cur_Position = Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) and then
                    (for all Idx in Cur_Position'Old .. Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) - 1 =>
                       Strng (Idx - Cur_Position'Old + 1) = The_File (Idx)) and then
                    Strng (Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old + 1) = ASCII.NUL and then
                    (for all Idx in Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old + 2 .. Strng'Last =>
                       Strng (Idx) = Strng'Old (Idx)) and then
                    --  redundant proposition to help automatic provers
                    No_Char_In_String (Strng, ASCII.LF, Find_Char_In_Slice (EOF_Ch, Cur_Position'Old, Cur_Position'Old + N - 2) - Cur_Position'Old + 1)

                 --  Case 4: both newline and EOF appear

                 --  In our model, we choose that this cannot occur. So we consider only
                 --  cases where EOF or newline character are repeated after the first
                 --  occurrence in the file.

                 else False)

                --  Failure corresponds to those cases where low-level fgets
                --  returns a NULL pointer: an error was issued, or the file is
                --  empty. In the last case Cur_Position is not modified.

                else
                  (Ferror (Stream) /= 0 or else
                  (Fpeek (Stream)'Old = EOF and then Cur_Position = Cur_Position'Old)));

   function ferror (stream : File_Descr) return int;

   procedure fgetc (stream : File_Descr; result : out int) with
     Global => (Proof_In => (The_File, EOF), In_Out => Cur_Position, Input => EOF_Ch),
     Post => (if The_File (Cur_Position'Old) = EOF_Ch then
                Cur_Position = Cur_Position'Old and then
                Result = EOF
              elsif The_File (Cur_Position'Old) = ASCII.LF then
                Cur_Position = Cur_Position'Old and then
                Result = Character'Pos (ASCII.LF)
              else
                Cur_Position = Cur_Position'Old + 1 and then
                Result = Character'Pos (The_File (Cur_Position'Old)));

private
   type File_Descr is new Integer;
end Helpers;
