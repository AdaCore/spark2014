----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with Ada.Text_IO;

package Protected_SPARK_IO_05
  with Initializes => SPARK_IO_PO
is
   type File_Type is private;

   type File_Mode is (In_File,
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
   Null_File : constant File_Type;

   function Standard_Output return File_Type
   with Global => null;

   protected type SPARK_IO_05 is
      pragma Priority(0);

      ---------------------
      -- File Management --
      ---------------------

      procedure Create
        (File         :    out File_Type;
         Name_Of_File : in     String;
         Form_Of_File : in     String;
         Status       :    out File_Status)
      with Depends => ((File, Status) => (Form_Of_File,
                                          Name_Of_File,
                                          SPARK_IO_05),
                       SPARK_IO_05 =>+ null);


      procedure Create_Flex
        (File         :    out File_Type;
         Name_Length  : in     Natural;
         Name_Of_File : in     String;
         Form_Of_File : in     String;
         Status       :    out File_Status)
      with Depends => ((File, Status) => (Form_Of_File,
                                          Name_Length,
                                          Name_Of_File,
                                          SPARK_IO_05),
                       SPARK_IO_05 =>+ null);


      procedure Open
        (File         :    out File_Type;
         Mode_Of_File : in     File_Mode;
         Name_Of_File : in     String;
         Form_Of_File : in     String;
         Status       :    out File_Status)
      with Depends => ((File, Status) => (Form_Of_File,
                                          Mode_Of_File,
                                          Name_Of_File,
                                          SPARK_IO_05),
                       SPARK_IO_05 =>+ null);

      procedure Open_Flex
        (File         :    out File_Type;
         Mode_Of_File : in     File_Mode;
         Name_Length  : in     Natural;
         Name_Of_File : in     String;
         Form_Of_File : in     String;
         Status       :    out File_Status)
      with Depends => ((File, SPARK_IO_05, Status) => (Form_Of_File,
                                                       Mode_Of_File,
                                                       Name_Length,
                                                       Name_Of_File,
                                                       SPARK_IO_05));

      procedure Close
        (File   : in out File_Type;
         Status :    out File_Status)
      with Depends => (File => null,
                       (SPARK_IO_05, Status) => (File, SPARK_IO_05));

      procedure Delete
        (File   : in out File_Type;
         Status :    out File_Status)
      with Depends => (File => null,
                       (SPARK_IO_05, Status) => (File, SPARK_IO_05));


      procedure Reset
        (File         : in out File_Type;
         Mode_Of_File : in     File_Mode;
         Status       :    out File_Status)
      with Depends => ((File, Status) => (File, Mode_Of_File),
                       SPARK_IO_05 =>+ null);

      function Valid_File (File : File_Type) return Boolean;

      function Mode (File : File_Type) return File_Mode;

      procedure Name
        (File         : in     File_Type;
         Name_Of_File :    out String;
         Stop         :    out Natural)
      with Depends => ((Name_Of_File, Stop) => File,
                       SPARK_IO_05 =>+ null);

      procedure Form
        (File         : in     File_Type;
         Form_Of_File :    out String;
         Stop         :    out Natural)
      with Depends => ((Form_Of_File, Stop) => File,
                       SPARK_IO_05 =>+ null);

      function Is_Open (File : File_Type) return Boolean;

      -----------------------------------------------
      -- Control of default input and output files --
      -----------------------------------------------

      --
      --  Not supported in SPARK_IO
      --

      --------------------------------------------
      -- Specification of line and page lengths --
      --------------------------------------------

      --
      --  Not supported in SPARK_IO
      --

      -----------------------------------
      -- Column, Line and Page Control --
      -----------------------------------

      procedure New_Line
        (File    : in File_Type;
         Spacing : in Positive)
      with Depends => (SPARK_IO_05 =>+ (File, Spacing));

      procedure Skip_Line
        (File    : in File_Type;
         Spacing : in Positive)
      with Depends => (SPARK_IO_05 =>+ (File, Spacing));

      procedure New_Page (File : in File_Type)
      with Depends => (SPARK_IO_05 =>+ File);

      function End_Of_Line (File : File_Type) return Boolean;

      function End_Of_File (File : File_Type) return Boolean;
      --  This is a potentially blocking function.
      --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

      procedure Set_In_File_Col
        (File : in File_Type;
         Posn : in Positive)
      with Depends => (SPARK_IO_05 =>+ (File, Posn)); --  ,
           --  Pre     => Mode (File) = In_File;

      procedure Set_Out_File_Col
        (File : in File_Type;
         Posn : in Positive)
      with Depends => (SPARK_IO_05 =>+ (File, Posn)); --  ,
           --  Pre     => Mode(File) = Out_File or Mode (File) = Append_File;

      function In_File_Col (File : File_Type) return Positive;
      --  with Pre => Mode (File) = In_File;
      --  This is a potentially blocking function.
      --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

      function Out_File_Col (File : File_Type) return Positive;
      --  with Pre => Mode (File) = Out_File or Mode (File) = Append_File;
      --  This is a potentially blocking function.
      --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

      function In_File_Line (File : File_Type) return Positive;
      --  with Pre => Mode (File) = In_File;
      --  This is a potentially blocking function.
      --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

      function Out_File_Line (File : File_Type) return Positive;
      --  with Pre => Mode (File) = Out_File or Mode (File) = Append_File;
      --  This is a potentially blocking function.
      --  DO NOT CALL THIS FUNCTION FROM A PROTECTED OPERATION.

      ----------------------------
      -- Character Input-Output --
      ----------------------------

      procedure Get_Char
        (File : in     File_Type;
         Item :    out Character)
      with Depends => ((Item, SPARK_IO_05) => (File, SPARK_IO_05));

      procedure Put_Char
        (File : in File_Type;
         Item : in Character)
      with Depends => (SPARK_IO_05 =>+ (File, Item));

      procedure Get_Char_Immediate
        (File   : in     File_Type;
         Item   :    out Character;
         Status :    out File_Status)
      with Depends => ((Item, SPARK_IO_05, Status) => (File, SPARK_IO_05));

      --  NOTE.  Only the variant of Get_Immediate that waits for a character to
      --  become available is supported.
      --  On return Status is one of Ok, Mode_Error or End_Error. See ALRM
      --  A.10.7 Item is Character'First if Status /= Ok

      -------------------------
      -- String Input-Output --
      -------------------------

      procedure Get_String
        (File : in     File_Type;
         Item :    out String;
         Stop :    out Natural)
      with Depends => ((Item, SPARK_IO_05, Stop) => (File, SPARK_IO_05));

      procedure Put_String
        (File : in File_Type;
         Item : in String;
         Stop : in Natural)
      with Depends => (SPARK_IO_05 =>+ (File, Item, Stop));

      procedure Get_Line
        (File : in     File_Type;
         Item :    out String;
         Stop :    out Natural)
      with Depends => ((Item, SPARK_IO_05, Stop) => (File, SPARK_IO_05));

      procedure Put_Line
        (File : in File_Type;
         Item : in String;
         Stop : in Natural)
      with Depends => (SPARK_IO_05 =>+ (File, Item, Stop));

      --------------------------
      -- Integer Input-Output --
      --------------------------

      --  SPARK_IO only supports input-output of
      --  the built-in integer type Integer

      procedure Get_Integer
        (File  : in     File_Type;
         Item  :    out Integer;
         Width : in     Natural;
         Read  :    out Boolean)
      with Depends => ((Item, Read, SPARK_IO_05) => (File, SPARK_IO_05, Width));

      procedure Put_Integer
        (File  : in File_Type;
         Item  : in Integer;
         Width : in Natural;
         Base  : in Number_Base)
      with Depends => (SPARK_IO_05 =>+ (Base, File, Item, Width));


      procedure Get_Int_From_String
        (Source    : in     String;
         Item      :    out Integer;
         Start_Pos : in     Positive;
         Stop      :    out Natural)
      with Depends => ((Item, Stop) => (Source, Start_Pos),
                       SPARK_IO_05 =>+ null);

      procedure Put_Int_To_String
        (Dest      : in out String;
         Item      : in     Integer;
         Start_Pos : in     Positive;
         Base      : in     Number_Base)
      with Depends => (Dest =>+ (Base, Item, Start_Pos),
                       SPARK_IO_05 =>+ null);

      ------------------------
      -- Float Input-Output --
      ------------------------

      --  SPARK_IO only supports input-output of
      --  the built-in real type Float

      procedure Get_Float
        (File  : in     File_Type;
         Item  :    out Float;
         Width : in     Natural;
         Read  :    out Boolean)
      with Depends => ((Item, Read, SPARK_IO_05) => (File, SPARK_IO_05, Width));

      procedure Put_Float
        (File : in File_Type;
         Item : in Float;
         Fore : in Natural;
         Aft  : in Natural;
         Exp  : in Natural)
      with Depends => (SPARK_IO_05 =>+ (Aft, Exp, File, Fore, Item));

      procedure Get_Float_From_String
        (Source    : in     String;
         Item      :    out Float;
         Start_Pos : in     Positive;
         Stop      :    out Natural)
      with Depends => ((Item, Stop) => (Source, Start_Pos),
                       SPARK_IO_05 =>+ null);

      procedure Put_Float_To_String
        (Dest      : in out String;
         Item      : in     Float;
         Start_Pos : in     Positive;
         Aft       : in     Natural;
         Exp       : in     Natural)
      with Depends => (Dest =>+ (Aft, Exp, Item, Start_Pos),
                       SPARK_IO_05 =>+ null);

   end SPARK_IO_05;

   SPARK_IO_PO : SPARK_IO_05;
private
   pragma SPARK_Mode (Off);

   type File_Descriptor is record
      File_Ref : Ada.Text_IO.File_Type;
   end record;
   type File_Type is access all File_Descriptor;

   Null_File : constant File_Type := null;
end Protected_SPARK_IO_05;
