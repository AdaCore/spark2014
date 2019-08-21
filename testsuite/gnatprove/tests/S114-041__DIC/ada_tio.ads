------------------------------------------------------------------------------
--                                                                          --
--                         GNAT RUN-TIME COMPONENTS                         --
--                                                                          --
--                          A D A . T E X T _ I O                           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 1992-2019, Free Software Foundation, Inc.         --
--                                                                          --
-- This specification is derived from the Ada Reference Manual for use with --
-- GNAT. The copyright notice above, and the license provisions that follow --
-- apply solely to the  contents of the part following the private keyword. --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- In particular,  you can freely  distribute your programs  built with the --
-- GNAT Pro compiler, including any required library run-time units,  using --
-- any licensing terms  of your choosing.  See the AdaCore Software License --
-- for full details.                                                        --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

--  Note: the generic subpackages of Text_IO (Integer_IO, Float_IO, Fixed_IO,
--  Modular_IO, Decimal_IO and Enumeration_IO) appear as private children in
--  GNAT. These children are with'ed automatically if they are referenced, so
--  this rearrangement is invisible to user programs, but has the advantage
--  that only the needed parts of Text_IO are processed and loaded.

with Ada.IO_Exceptions;
with Ada.Streams;

with System;
with System.WCh_Con;

package Ada_TIO with
  Abstract_State => (Current_Files_Handling, File_System),
  Initializes => (Current_Files_Handling, File_System)
is
   pragma Elaborate_Body;

   type File_Type is limited private with
     Default_Initial_Condition => (not Is_Open (File_Type));
   type File_Mode is (In_File, Out_File, Append_File);

   --  The following representation clause allows the use of unchecked
   --  conversion for rapid translation between the File_Mode type
   --  used in this package and System.File_IO.

   for File_Mode use
     (In_File     => 0,  -- System.FIle_IO.File_Mode'Pos (In_File)
      Out_File    => 2,  -- System.File_IO.File_Mode'Pos (Out_File)
      Append_File => 3); -- System.File_IO.File_Mode'Pos (Append_File)

   type Count is range 0 .. Natural'Last;
   --  The value of Count'Last must be large enough so that the assumption that
   --  the Line, Column and Page counts can never exceed this value is valid.

   subtype Positive_Count is Count range 1 .. Count'Last;

   Unbounded : constant Count := 0;
   --  Line and page length

   subtype Field is Integer range 0 .. 255;
   --  Note: if for any reason, there is a need to increase this value, then it
   --  will be necessary to change the corresponding value in System.Img_Real
   --  in file s-imgrea.adb.

   subtype Number_Base is Integer range 2 .. 16;

   type Type_Set is (Lower_Case, Upper_Case);

   ---------------------
   -- File Management --
   ---------------------

   procedure Create
     (File : in out File_Type;
      Mode : File_Mode := Out_File;
      Name : String := "";
      Form : String := "")
   with
     Pre => not Is_Open (File),
     Post => Is_Open (File) and then Ada_TIO.Mode (File) = Mode,
     Global => (In_Out => File_System);

   procedure Open
     (File : in out File_Type;
      Mode : File_Mode;
      Name : String;
      Form : String := "")
   with
     Pre => not Is_Open (File),
     Post => Is_Open (File) and then Ada_TIO.Mode (File) = Mode,
     Global => null;

   procedure Close  (File : in out File_Type) with
     Pre => Is_Open (File),
     Post => not Is_Open (File),
     Global => (In_Out => File_System);
   procedure Delete (File : in out File_Type) with
     Pre => Is_Open (File),
     Post => not Is_Open (File),
     Global => (In_Out => File_System);
   procedure Reset  (File : in out File_Type; Mode : File_Mode) with
     Pre => Is_Open (File),
     Post => Is_Open (File) and then Ada_TIO.Mode (File) = Mode,
     Global => (In_Out => File_System);
   procedure Reset  (File : in out File_Type) with
     Pre => Is_Open (File),
     Post => Is_Open (File) and Mode (File)'Old = Mode (File),
     Global => (In_Out => File_System);

   function Mode (File : File_Type) return File_Mode with
     Pre => Is_Open (File),
     Global => null;
   function Name (File : File_Type) return String with
     Pre => Is_Open (File),
     Global => null;
   function Form (File : File_Type) return String with
     Pre => Is_Open (File),
     Global => null;

   function Is_Open (File : File_Type) return Boolean with
     Global => null;

   ------------------------------------------------------
   -- Control of default input, output and error files --
   ------------------------------------------------------

   procedure Set_Input  (File : File_Type) with SPARK_Mode => Off;
   procedure Set_Output (File : File_Type) with SPARK_Mode => Off;
   procedure Set_Error  (File : File_Type) with SPARK_Mode => Off;

   function Standard_Input  return File_Type with SPARK_Mode => Off;
   function Standard_Output return File_Type with SPARK_Mode => Off;
   function Standard_Error  return File_Type with SPARK_Mode => Off;

   function Current_Input  return File_Type with SPARK_Mode => Off;
   function Current_Output return File_Type with SPARK_Mode => Off;
   function Current_Error  return File_Type with SPARK_Mode => Off;

   type File_Access is access constant File_Type;

   function Standard_Input  return File_Access with SPARK_Mode => Off;
   function Standard_Output return File_Access with SPARK_Mode => Off;
   function Standard_Error  return File_Access with SPARK_Mode => Off;

   function Current_Input  return File_Access with SPARK_Mode => Off;
   function Current_Output return File_Access with SPARK_Mode => Off;
   function Current_Error  return File_Access with SPARK_Mode => Off;

   --------------------
   -- Buffer control --
   --------------------

   --  Note: The parameter file is IN OUT in the RM, but this is clearly
   --  an oversight, and was intended to be IN, see AI95-00057.

   procedure Flush (File : File_Type) with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => (In_Out => File_System);
   procedure Flush with
     Global => (In_Out => (Current_Files_Handling, File_System));

   --------------------------------------------
   -- Specification of line and page lengths --
   --------------------------------------------

   procedure Set_Line_Length (File : File_Type; To : Count) with
     Pre => Is_Open (File)  and then Mode (File) /= In_File,
     Post => Line_Length (File) = To,
     Global => (In_Out => File_System);
   procedure Set_Line_Length (To : Count) with
     Post => Line_Length = To,
     Global => (In_Out => (Current_Files_Handling, File_System));

   procedure Set_Page_Length (File : File_Type; To : Count) with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Post => Page_Length (File) = To,
     Global => (In_Out => File_System);
   procedure Set_Page_Length (To : Count) with
     Post => Page_Length = To,
     Global => (In_Out => (Current_Files_Handling, File_System));

   function Line_Length (File : File_Type) return Count with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => null;
   function Line_Length return Count with
     Global => (Input => Current_Files_Handling);

   function Page_Length (File : File_Type) return Count with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => null;
   function Page_Length return Count with
     Global => (Input => Current_Files_Handling);

   ------------------------------------
   -- Column, Line, and Page Control --
   ------------------------------------

   procedure New_Line (File : File_Type; Spacing : Positive_Count := 1) with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => (In_Out => File_System);
   procedure New_Line (Spacing : Positive_Count := 1) with
     Global => (In_Out => (Current_Files_Handling, File_System));

   procedure Skip_Line (File : File_Type; Spacing : Positive_Count := 1) with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (In_Out => File_System);
   procedure Skip_Line (Spacing : Positive_Count := 1) with
     Global => (In_Out => (Current_Files_Handling, File_System));

   function End_Of_Line (File : File_Type) return Boolean with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);
   function End_Of_Line return Boolean with
     Global => (Input => (Current_Files_Handling, File_System));

   procedure New_Page (File : File_Type) with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => (In_Out => File_System);
   procedure New_Page with
     Global => (In_Out => (Current_Files_Handling, File_System));

   procedure Skip_Page (File : File_Type) with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (In_Out => File_System);
   procedure Skip_Page with
     Global => (In_Out => (Current_Files_Handling, File_System));

   function End_Of_Page (File : File_Type) return Boolean with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);
   function End_Of_Page return Boolean with
     Global => (Input => (Current_Files_Handling, File_System));

   function End_Of_File (File : File_Type) return Boolean with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);
   function End_Of_File return Boolean with
     Global => (Input => (Current_Files_Handling, File_System));

   procedure Set_Col (File : File_Type;  To : Positive_Count) with
     Pre =>
       Is_Open (File)
       and then ((Mode (File) /= In_File
                  and then (Line_Length (File) = 0
                            or else To <= Line_Length (File)))
                 or else (Mode (File) = In_File)),
     Global => (In_Out => File_System);
   procedure Set_Col (To : Positive_Count) with
     Pre => Line_Length = 0 or else To <= Line_Length,
     Global => (Input => (Current_Files_Handling, File_System));

   procedure Set_Line (File : File_Type; To : Positive_Count) with
     Pre =>
       Is_Open (File)
       and then ((Mode (File) /= In_File
                  and then (Page_Length (File) = 0
                            or else To <= Page_Length (File)))
                 or else (Mode (File) = In_File)),
     Global => (In_Out => File_System);
   procedure Set_Line (To : Positive_Count) with
     Pre => Page_Length = 0 or else To <= Page_Length,
     Global => (Input => (Current_Files_Handling, File_System));

   function Col (File : File_Type) return Positive_Count with
     Global => (Input => File_System);
   function Col return Positive_Count with
     Global => (Input => (Current_Files_Handling, File_System));

   function Line (File : File_Type) return Positive_Count with
     Global => (Input => File_System);
   function Line return Positive_Count with
     Global => (Input => (Current_Files_Handling, File_System));

   function Page (File : File_Type) return Positive_Count with
     Global => (Input => File_System);
   function Page return Positive_Count with
     Global => (Input => (Current_Files_Handling, File_System));

   ----------------------------
   -- Character Input-Output --
   ----------------------------

   procedure Get (File : File_Type; Item : out Character) with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);
   procedure Get (Item : out Character) with
     Global => (Input => File_System,
                In_Out => Current_Files_Handling);
   procedure Put (File : File_Type; Item : Character) with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => (In_Out => File_System);
   procedure Put (Item : Character) with
     Global => (In_Out => (Current_Files_Handling, File_System));

   procedure Look_Ahead
     (File        : File_Type;
      Item        : out Character;
      End_Of_Line : out Boolean)
   with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);

   procedure Look_Ahead
     (Item        : out Character;
      End_Of_Line : out Boolean)
   with
     Global => (Input => File_System,
               In_Out => Current_Files_Handling);

   procedure Get_Immediate
     (File : File_Type;
      Item : out Character)
   with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);

   procedure Get_Immediate
     (Item : out Character)
   with
     Global => (Input => (Current_Files_Handling, File_System));

   procedure Get_Immediate
     (File      : File_Type;
      Item      : out Character;
      Available : out Boolean)
   with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);

   procedure Get_Immediate
     (Item      : out Character;
      Available : out Boolean)
   with
     Global => (Input => (Current_Files_Handling, File_System));

   -------------------------
   -- String Input-Output --
   -------------------------

   procedure Get (File : File_Type; Item : out String) with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);
   procedure Get (Item : out String) with
     Global => (Input => File_System,
                In_Out => Current_Files_Handling);
   procedure Put (File : File_Type; Item : String) with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => (In_Out => File_System);
   procedure Put (Item : String) with
     Global => (In_Out => (Current_Files_Handling, File_System));

   procedure Get_Line
     (File : File_Type;
      Item : out String;
      Last : out Natural)
   with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);

   procedure Get_Line
     (Item : out String;
      Last : out Natural)
   with
     Global => (Input => File_System,
                In_Out => Current_Files_Handling);

   function Get_Line (File : File_Type) return String with
     Pre => Is_Open (File) and then Mode (File) = In_File,
     Global => (Input => File_System);
   pragma Ada_05 (Get_Line);

   function Get_Line return String with
     SPARK_Mode => Off,
     Global => (Input => File_System,
                In_Out => Current_Files_Handling);
   pragma Ada_05 (Get_Line);

   procedure Put_Line
     (File : File_Type;
      Item : String)
   with
     Pre => Is_Open (File) and then Mode (File) /= In_File,
     Global => (In_Out => File_System);

   procedure Put_Line
     (Item : String)
   with
     Global => (In_Out => (Current_Files_Handling, File_System));

   ---------------------------------------
   -- Generic packages for Input-Output --
   ---------------------------------------

   --  The generic packages:

   --    Ada.Text_IO.Integer_IO
   --    Ada.Text_IO.Modular_IO
   --    Ada.Text_IO.Float_IO
   --    Ada.Text_IO.Fixed_IO
   --    Ada.Text_IO.Decimal_IO
   --    Ada.Text_IO.Enumeration_IO

   --  are implemented as separate child packages in GNAT, so the
   --  spec and body of these packages are to be found in separate
   --  child units. This implementation detail is hidden from the
   --  Ada programmer by special circuitry in the compiler that
   --  treats these child packages as though they were nested in
   --  Text_IO. The advantage of this special processing is that
   --  the subsidiary routines needed if these generics are used
   --  are not loaded when they are not used.

private

   --  The following procedures have a File_Type formal of mode IN OUT because
   --  they may close the original file. The Close operation may raise an
   --  exception, but in that case we want any assignment to the formal to
   --  be effective anyway, so it must be passed by reference (or the caller
   --  will be left with a dangling pointer).

   pragma Export_Procedure
     (Internal  => Close,
      External  => "",
      Mechanism => Reference);
   pragma Export_Procedure
     (Internal  => Delete,
      External  => "",
      Mechanism => Reference);
   pragma Export_Procedure
     (Internal        => Reset,
      External        => "",
      Parameter_Types => (File_Type),
      Mechanism       => Reference);
   pragma Export_Procedure
     (Internal        => Reset,
      External        => "",
      Parameter_Types => (File_Type, File_Mode),
      Mechanism       => (File => Reference));

   -----------------------------------
   -- Handling of Format Characters --
   -----------------------------------

   --  Line marks are represented by the single character ASCII.LF (16#0A#).
   --  In DOS and similar systems, underlying file translation takes care
   --  of translating this to and from the standard CR/LF sequences used in
   --  these operating systems to mark the end of a line. On output there is
   --  always a line mark at the end of the last line, but on input, this
   --  line mark can be omitted, and is implied by the end of file.

   --  Page marks are represented by the single character ASCII.FF (16#0C#),
   --  The page mark at the end of the file may be omitted, and is normally
   --  omitted on output unless an explicit New_Page call is made before
   --  closing the file. No page mark is added when a file is appended to,
   --  so, in accordance with the permission in (RM A.10.2(4)), there may
   --  or may not be a page mark separating preexisting text in the file
   --  from the new text to be written.

   --  A file mark is marked by the physical end of file. In DOS translation
   --  mode on input, an EOF character (SUB = 16#1A#) gets translated to the
   --  physical end of file, so in effect this character is recognized as
   --  marking the end of file in DOS and similar systems.

   LM : constant := Character'Pos (ASCII.LF);
   --  Used as line mark

   PM : constant := Character'Pos (ASCII.FF);
   --  Used as page mark, except at end of file where it is implied

   --------------------------------
   -- Text_IO File Control Block --
   --------------------------------

   Default_WCEM : System.WCh_Con.WC_Encoding_Method :=
                    System.WCh_Con.WCEM_UTF8;
   --  This gets modified during initialization (see body) using
   --  the default value established in the call to Set_Globals.

   type Text_AFCB;
   type File_Type is access all Text_AFCB;

   type Text_AFCB is null record;

   procedure AFCB_Close (File : not null access Text_AFCB);
   procedure AFCB_Free  (File : not null access Text_AFCB);

   procedure Read
     (File : in out Text_AFCB;
      Item : out Ada.Streams.Stream_Element_Array;
      Last : out Ada.Streams.Stream_Element_Offset);
   --  Read operation used when Text_IO file is treated directly as Stream

   procedure Write
     (File : in out Text_AFCB;
      Item : Ada.Streams.Stream_Element_Array);
   --  Write operation used when Text_IO file is treated directly as Stream

   ------------------------
   -- The Standard Files --
   ------------------------

   Standard_In_AFCB  : aliased Text_AFCB;
   Standard_Out_AFCB : aliased Text_AFCB;
   Standard_Err_AFCB : aliased Text_AFCB;

   Standard_In  : aliased File_Type := Standard_In_AFCB'Access with
     Part_Of => File_System;
   Standard_Out : aliased File_Type := Standard_Out_AFCB'Access with
     Part_Of => File_System;
   Standard_Err : aliased File_Type := Standard_Err_AFCB'Access with
     Part_Of => File_System;
   --  Standard files

   Current_In   : aliased File_Type := Standard_In with
     Part_Of => File_System;
   Current_Out  : aliased File_Type := Standard_Out with
     Part_Of => File_System;
   Current_Err  : aliased File_Type := Standard_Err with
     Part_Of => File_System;
   --  Current files

   function EOF_Char return Integer;
   --  Returns the system-specific character indicating the end of a text file.
   --  This is exported for use by child packages such as Enumeration_Aux to
   --  eliminate their needing to depend directly on Interfaces.C_Streams,
   --  which is not available in certain target environments (such as AAMP).

   procedure Initialize_Standard_Files;
   --  Initializes the file control blocks for the standard files. Called from
   --  the elaboration routine for this package, and from Reset_Standard_Files
   --  in package Ada.Text_IO.Reset_Standard_Files.

end Ada_TIO;
