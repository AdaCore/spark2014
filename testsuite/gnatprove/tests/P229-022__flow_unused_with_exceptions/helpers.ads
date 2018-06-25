with Interfaces.C_Streams;    use Interfaces.C_Streams;

package Helpers with SPARK_Mode is
   type File_Descr is private;

   The_File     : String (Positive) with Ghost;
   Cur_Position : Positive with Ghost;

   EOF_Ch : constant Character := Character'Val (EOF mod 256);

   function ferror (stream : File_Descr) return int;

   procedure fgetc (stream : File_Descr; result : out int) with
     Global => (Proof_In => (The_File, EOF), In_Out => Cur_Position),
     Post => (if Result /= EOF then
                Cur_Position = Cur_Position'Old + 1 and then
                Result = Character'Pos (The_File (Cur_Position'Old)));

   procedure ungetc (c : int; stream : File_Descr; result : out int) with
     Global => (In_Out => (The_File, Cur_Position), Proof_In => EOF),
     Post => (if Result /= EOF then
                Cur_Position = Cur_Position'Old - 1 and then
                The_File = The_File'Old'Update (Cur_Position => Character'Val (C)));

private
   type File_Descr is new Integer;
end Helpers;
