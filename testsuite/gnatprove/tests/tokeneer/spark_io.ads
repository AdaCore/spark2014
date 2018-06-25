------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

with Ada.Text_IO;

package Spark_IO
  with SPARK_Mode,
       Abstract_State => (State,
                          Inputs,
                          Outputs),
       Initializes    => (State,
                          Inputs,
                          Outputs)
is

  type File_Type   is private; --718 removed limited
  type File_Mode   is (In_File,
                       Out_File,
                       Append_File);
  type File_Status is (Ok,
                       Status_Error,
                       Mode_Error,
                       Name_Error,
                       Use_Error,
                       Device_Error,
                       End_Error,
                       Data_Error,
                       Layout_Error,
                       Storage_Error,
                       Program_Error);

  subtype Number_Base is Integer range 2 .. 16;

  Standard_Input  : constant File_Type;
  Standard_Output : constant File_Type;
  Null_File       : constant File_Type; --718


-- File Management

  procedure Create (File         :    out File_Type;
                    Name_Of_File : in     String;
                    Form_Of_File : in     String;
                    Status       :    out File_Status)
    with Global  => (In_Out => State),
         Depends => ((State,
                      File,
                      Status) => (State,
                                  Name_Of_File,
                                  Form_Of_File));

  procedure Open (File         :    out File_Type;
                  Mode_Of_File : in     File_Mode;
                  Name_Of_File : in     String;
                  Form_Of_File : in     String;
                  Status       :    out File_Status)
    with Global  => (In_Out => State),
         Depends => ((State,
                      File,
                      Status) => (State,
                                  Mode_Of_File,
                                  Name_Of_File,
                                  Form_Of_File));

  procedure Close (File   : in     File_Type;
                   Status :    out File_Status)
    with Global  => (In_Out => State),
         Depends => ((State,
                      Status) => (State,
                                  File));

  procedure Delete (File   : in     File_Type;
                    Status :    out File_Status)
    with Global  => (In_Out => State),
         Depends => ((State,
                      Status) => (State,
                                  File));

  procedure Reset (File         : in out File_Type;
                   Mode_Of_File : in     File_Mode;
                   Status       :    out File_Status)
    with Global  => null,
         Depends => ((File,
                      Status) => (File,
                                  Mode_Of_File));

  function Valid_File (File : File_Type) return Boolean
    with Global => null;

  function Mode (File : File_Type) return File_Mode
    with Global => State;

  procedure Name (File         : in     File_Type;
                  Name_Of_File :    out String;
                  Stop         :    out Natural)
    with Global  => null,
         Depends => ((Name_Of_File,
                       Stop)        => (File,
                                        Name_Of_File));

  procedure Form (File         : in     File_Type;
                  Form_Of_File :    out String;
                  Stop         :    out Natural)
    with Global  => null,
         Depends => ((Form_Of_File,
                      Stop)         => (File,
                                        Form_Of_File));

  function Is_Open (File : File_Type) return Boolean
    with Global => State;

-- Control of default input and output Files

  --
  -- Not supported in Spark_IO
  --

-- Specification of line and page lengths

  --
  -- Not supported in Spark_IO
  --


-- Column, Line and Page Control

  procedure New_Line (File    : in File_Type;
                      Spacing : in Positive)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                 File,
                                 Spacing));

  procedure Skip_Line (File    : in File_Type;
                       Spacing : in Positive)
    with Global  => (In_Out => Inputs),
         Depends => (Inputs => (Inputs,
                                File,
                                Spacing));

  procedure New_Page (File : in File_Type)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                 File));

  function End_Of_Line (File : File_Type) return Boolean
    with Global => Inputs;

  function End_Of_File (File : File_Type) return Boolean
    with Global => Inputs;

  procedure Set_In_File_Col (File : in File_Type;
                             Posn : in Positive)
    with Global  => (In_Out => Inputs, Input => State),
         Depends => (Inputs => (Inputs,
                                File,
                                Posn,
                                State)),
         Pre     => Mode (File) = In_File;

  procedure Set_Out_File_Col (File : in File_Type;
                              Posn : in Positive)
    with Global  => (In_Out => Outputs, Input => State),
         Depends => (Outputs => (Outputs,
                                 File,
                                 Posn,
                                 State)),
         Pre     => Mode (File) = Out_File or else
                      Mode (File) = Append_File;

  function In_File_Col (File : File_Type) return Positive
    with Global => (Inputs, State),
         Pre    => Mode (File) = In_File;

  function Out_File_Col (File : File_Type) return Positive
    with Global => (Outputs, State),
         Pre    => Mode (File) = Out_File or else
                     Mode (File) = Append_File;

  function In_File_Line (File : File_Type) return Positive
    with Global => (Inputs, State),
         Pre    => Mode (File) = In_File;

  function Out_File_Line (File : File_Type) return Positive
    with Global => (Outputs, State),
         Pre    => Mode (File) = Out_File or else
                     Mode (File) = Append_File;

-- Character Input-Output

  procedure Get_Char (File : in     File_Type;
                      Item :    out Character)
    with Global  => (In_Out => Inputs),
         Depends => ((Inputs,
                      Item)   => (Inputs,
                                  File));

  procedure Put_Char (File : in File_Type;
                      Item : in Character)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                  File,
                                  Item));

-- String Input-Output

  procedure Get_String (File : in     File_Type;
                        Item :    out String;
                        Stop :    out Natural)
    with Global  => (In_Out => Inputs),
         Depends => ((Inputs,
                      Item,
                      Stop)   => (Inputs,
                                  File,
                                  Item));

  procedure Put_String (File : in File_Type;
                        Item : in String;
                        Stop : in Natural)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                 File,
                                 Item,
                                 Stop));

  procedure Get_Line (File : in     File_Type;
                      Item :    out String;
                      Stop :    out Natural)
    with Global  => (In_Out => Inputs),
         Depends => ((Inputs,
                      Item,
                      Stop)   => (Inputs,
                                  File,
                                  Item));

  procedure Put_Line (File : in File_Type;
                      Item : in String;
                      Stop : in Natural)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                 File,
                                 Item,
                                 Stop));

-- Integer Input-Output

  -- Spark_IO only supports input-output of
  -- the built-in Integer type Integer

  procedure Get_Integer (File  : in     File_Type;
                         Item  :    out Integer;
                         Width : in     Natural;
                         Read  :    out Boolean)
    with Global  => (In_Out => Inputs),
         Depends => ((Inputs,
                      Item,
                      Read)   => (Inputs,
                                  File,
                                  Width));

  procedure Put_Integer (File  : in File_Type;
                         Item  : in Integer;
                         Width : in Natural;
                         Base  : in Number_Base)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                 File,
                                 Item,
                                 Width,
                                 Base));

  procedure Get_Int_From_String (Source    : in     String;
                                 Item      :    out Integer;
                                 Start_Pos : in     Positive;
                                 Stop      :    out Natural)
    with Global  => null,
         Depends => ((Item,
                      Stop) => (Source,
                                Start_Pos));

  procedure Put_Int_To_String (Dest      : in out String;
                               Item      : in     Integer;
                               Start_Pos : in     Positive;
                               Base      : in     Number_Base)
    with Global  => null,
         Depends => (Dest => (Dest,
                              Item,
                              Start_Pos,
                              Base));

-- Float Input-Output

  -- Spark_IO only supports input-output of
  -- the built-in real type Float

  procedure Get_Float (File  : in     File_Type;
                       Item  :    out Float;
                       Width : in     Natural;
                       Read  :    out Boolean)
    with Global  => (In_Out => Inputs),
         Depends => ((Inputs,
                      Item,
                      Read)   => (Inputs,
                                  File,
                                  Width));

  procedure Put_Float (File : in File_Type;
                       Item : in Float;
                       Fore : in Natural;
                       Aft  : in Natural;
                       Exp  : in Natural)
    with Global  => (In_Out => Outputs),
         Depends => (Outputs => (Outputs,
                                 File,
                                 Item,
                                 Fore,
                                 Aft,
                                 Exp));

  procedure Get_Float_From_String (Source    : in     String;
                                   Item      :    out Float;
                                   Start_Pos : in     Positive;
                                   Stop      :    out Natural)
    with Global  => null,
         Depends => ((Item,
                      Stop) => (Source,
                                Start_Pos));

  procedure Put_Float_To_String (Dest      : in out String;
                                 Item      : in     Float;
                                 Start_Pos : in     Positive;
                                 Aft       : in     Natural;
                                 Exp       : in     Natural)
    with Global  => null,
         Depends => (Dest => (Dest,
                              Item,
                              Start_Pos,
                              Aft,
                              Exp));

private
  pragma SPARK_Mode (Off);

  type IO_TYPE  is (Stdin, Stdout, NamedFile);
  type File_PTR is access Ada.Text_IO.File_Type;

  -- In addition to the fields listed here, we consider the
  -- FILE_PTR.all record to contain the name and mode of the
  -- file from the point of view of the annotations above.
  type File_Type is record
     File    : File_Ptr := null;
     IO_Sort : IO_Type  := NamedFile;
  end record;

  Standard_Input  : constant File_Type := File_Type'(null, StdIn);
  Standard_Output : constant File_Type := File_Type'(null, StdOut);
  Null_File       : constant File_Type := File_Type'(null, NamedFile); --718
end Spark_IO;
