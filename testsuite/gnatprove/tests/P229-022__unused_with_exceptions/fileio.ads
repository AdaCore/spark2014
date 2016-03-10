with Interfaces.C_Streams;    use Interfaces.C_Streams;
with Helpers; use Helpers;

package Fileio with SPARK_Mode is

   type File_Type is record
     Descr : File_Descr;
     Before_LM : Boolean;
     Before_LM_PM : Boolean;
     Is_Regular_File : Boolean;
   end record;

   Device_Error : exception;

   procedure Simple (X, Y : in out Integer);

   procedure Simple2 (X, Y : in out Integer);

   procedure Getc (File : File_Type; Ch : out Int) with
     Global => (Input => (EOF, The_File), In_Out => Cur_Position),
     Post => Ch = Character'Pos (The_File (Cur_Position'Old)) and then
             Cur_Position = Cur_Position'Old + 1;
   --  Gets next character from file, which has already been checked for being
   --  in read status, and returns the character read if no error occurs. The
   --  result is EOF if the end of file was read.

   procedure Ungetc (ch : int; File : File_Type) with
     Global => (Input => EOF, In_Out => (The_File, Cur_Position)),
     Post => The_File = The_File'Old'Update (Cur_Position'Old => Character'Val (Ch)) and then
             Cur_Position = Cur_Position'Old - 1;
   --  Pushes back character into stream, using ungetc. The caller has checked

end Fileio;
