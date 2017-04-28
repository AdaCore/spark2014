with Helpers; use Helpers;
with Interfaces.C_Streams;    use Interfaces.C_Streams;

package TextIO with
  SPARK_Mode,
  Abstract_State => Current_Input_File
is

   type File_Type is private;

   procedure Get_Line
     (File : in out File_Type;
      Item : out String;
      Last : out Natural)
   with
     Global => (Input => (EOF, EOF_Ch, The_File), In_Out => (Cur_Position)),

     --  It is an error to call Get_Line on an empty file

     Pre  => not End_Of_File (File),

     Contract_Cases =>

       --  If Item is empty, return Item'First - 1 in Last

       (Item'Last < Item'First =>
          Last = Item'First - 1,

        --  Otherwise, return in Last the length of the string copied, which
        --  may be filling Item, or up to EOF or newline character.

        others =>
          (Last = Item'First - 1 or Last in Item'Range) and then
          (for all Idx in Item'First .. Last =>
             Item (Idx) = The_File (Idx - Item'First + Cur_Position'Old)) and then
          Cur_Position = Cur_Position'Old + Last - Item'First + 1 and then
          (Last = Item'Last or else
           The_File (Cur_Position) = EOF_Ch or else
           The_File (Cur_Position) = ASCII.LF));

   procedure Get_Line
     (Item : out String;
      Last : out Natural)
   with
     Global => (Input => (EOF, EOF_Ch, The_File), In_Out => (Cur_Position, Current_Input_File)),

     --  It is an error to call Get_Line on an empty file

     Pre  => not End_Of_File (Current_File),

     Contract_Cases =>

       --  If Item is empty, return Item'First - 1 in Last

       (Item'Last < Item'First =>
          Last = Item'First - 1,

        --  Otherwise, return in Last the length of the string copied, which
        --  may be filling Item, or up to EOF or newline character.

        others =>
          (Last = Item'First - 1 or Last in Item'Range) and then
          (for all Idx in Item'First .. Last =>
             Item (Idx) = The_File (Idx - Item'First + Cur_Position'Old)) and then
          Cur_Position = Cur_Position'Old + Last - Item'First + 1 and then
          (Last = Item'Last or else
           The_File (Cur_Position) = EOF_Ch or else
           The_File (Cur_Position) = ASCII.LF));

   --  Because functions are not allowed to have side-effects in SPARK, and
   --  out model forces Get_Line to update global ghost variable Cur_Position,
   --  transform function Get_Line into a procedure Get_Line_Function to check
   --  absence of run-time errors and functional contract on the equivalent
   --  procedure.

   procedure Get_Line_Function (File : in out File_Type; Result : out String; Num : out Natural) with

     --  It is an error to call Get_Line on an empty file

     Pre => not End_Of_File (File) and then

            --  Pretend that we are passing a huge Result string of size
            --  Positive. This is an effect of making Get_Line function a
            --  procedure for formal verification.

            Result'First = 1 and then
            Result'Last = Positive'Last,

     --  Return in Num the length of the string copied, up to EOF or newline
     --  character.

     Post => (for all Idx in 1 .. Num =>
                Result (Idx) = The_File (Idx - 1 + Cur_Position'Old)) and then
             Cur_Position = Cur_Position'Old + Num and then
             (The_File (Cur_Position) = EOF_Ch or else
              The_File (Cur_Position) = ASCII.LF);

   Device_Error : exception;
   End_Error : exception;

   type Count is range 0 .. Natural'Last;
   --  The value of Count'Last must be large enough so that the assumption that
   --  the Line, Column and Page counts can never exceed this value is valid.

   LM : constant := Character'Pos (ASCII.LF);
   --  Used as line mark
   PM : constant := Character'Pos (ASCII.FF);
   --  Used as page mark, except at end of file where it is implied

   function End_Of_File (File : File_Type) return Boolean with
     Post => End_Of_File'Result = (Fpeek (File) = EOF)
#if TEST_GET_LINE
     ;
#else
     , Import;
#end if;

   function Fpeek (File : File_Type) return Int
#if TEST_GET_LINE
   ;
#else
   with Ghost;
#end if;

   function Current_File return File_Type;

private

   type File_Type is record
     Descr : File_Descr;
     Before_LM : Boolean;
     Before_LM_PM : Boolean;
     Col : Count;
     Line : Count;
     Page : Count;
     Is_Regular_File : Boolean;
   end record;

#if TEST_GET_LINE
   function End_Of_File (File : File_Type) return Boolean
     is (Fpeek (File) = EOF);
#end if;

   function Fpeek (File : File_Type) return Int is (Fpeek (File.Descr));

   Current_In   : File_Type with Part_Of => Current_Input_File;

   function Current_File return File_Type is (Current_In);

end TextIO;
