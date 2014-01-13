--  A reduced testcase  --

with Ada.Text_IO;

package Spark_IO
  with SPARK_Mode,
        Abstract_State => (State, Inputs, Outputs),
        Initializes    => (State, Inputs, Outputs)
is

  type File_Type is private; --718 removed limited
  type File_Mode is (In_File, Out_File, Append_File);
  type File_Status is (Ok, Status_Error, Mode_Error, Name_Error, Use_Error,
                       Device_Error, End_Error,  Data_Error, Layout_Error,
                       Storage_Error, Program_Error);

  subtype Number_Base is Integer range 2 .. 16;

  Standard_Input  : constant File_Type;
  Standard_Output : constant File_Type;
  Null_File       : constant File_Type; --718

  function Mode(File : File_Type) return File_Mode;

  function In_File_Col(File : File_Type) return Positive
     with Global => Inputs,
          Pre    => Mode (File) = In_File;

private
  pragma SPARK_Mode (Off);

  type IO_TYPE   is (Stdin, Stdout, NamedFile);
  type File_PTR  is access Ada.Text_IO.File_Type;

  -- In addition to the fields listed here, we consider the
  -- FILE_PTR.all record to contain the name and mode of the
  -- file from the point of view of the annotations above.
  type File_Type is
     record
        File    : File_Ptr := null;
        IO_Sort : IO_Type  := NamedFile;
     end record;

  Standard_Input  : constant File_Type := File_Type'(null, StdIn);
  Standard_Output : constant File_Type := File_Type'(null, StdOut);
  Null_File       : constant File_Type := File_Type'(null, NamedFile); --718
end Spark_IO;
