------------------------------------------------------------------------------
--                                                                          --
--                           SPARK_IO EXAMPLES                              --
--                                                                          --
--                     Copyright (C) 2013, Altran UK                        --
--                                                                          --
-- SPARK is free software;  you can redistribute it  and/or modify it under --
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
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------

pragma SPARK_Mode (On);

package SPARK.Text_IO
  with Initializes => (Standard_Input, Standard_Output, Standard_Error),
       Initial_Condition => Is_Readable (Standard_Input) and
                            Is_Writable (Standard_Output) and
                            Is_Writable (Standard_Error) and
                            Status (Standard_Input) = Success and
                            Status (Standard_Output) = Success and
                            Status (Standard_Error) = Success
is
   type File_Type   is new SPARK.Text_IO_File_Type;
   type File_Status is new SPARK.File_Status;
   type File_Mode   is new Ada.Text_IO.File_Mode;
   type Count       is new Ada.Text_IO.Count;
   subtype Positive_Count is Count range 1 .. Count'Last;

   subtype Field       is Integer range 0 .. Ada.Text_IO.Field'Last;
   subtype Number_Base is Integer range 2 .. 16;

   type Type_Set is new Ada.Text_IO.Type_Set;

   type Count_Result (Status : File_Status := Status_Error) is record
      case Status is
         when Success => Value : Count;
         when others => null;
      end case;
   end record;

   type Character_Result (Status : File_Status := Status_Error) is record
      case Status is
         when Success => Item : Character;
         when others => null;
      end case;
   end record;

   type Immediate_Result
     (Status : File_Status := Status_Error;
      Available : Boolean  := False) is record
      case Status is
         when Success =>
            case Available is
               when True => Item : Character;
               when others => null;
            end case;
         when others => null;
      end case;
   end record;

   --  Standard_Input, Standard_Output and Standard_Error are variables because
   --  many of the file operations now have an in out parameter for the file.
   --  The variables cannot be directly altered, copied or compared as they
   --  are of a limited type and so that a client of the package cannot misuse
   --  them.

   Standard_Input,
   Standard_Output,
   Standard_Error : File_Type;

   --  The status of the last operation on a file may be obtained by calling
   --  the function Status declared below.
   function Status (File : File_Type) return File_Status
     with Global => null;

   --  There are restrictions on what can be done with the standard files,
   --  Standard_Input, Standard_Output and Standard_Error.  For instance
   --  they cannot be opened or closed or reset (this not allowed in Ada).
   function Is_Standard_Input (File : File_Type) return Boolean
     with Global     => null,
          Convention => Ghost;

   function Is_Standard_Output (File : File_Type) return Boolean
     with Global     => null,
          Convention => Ghost;

   function Is_Standard_Error (File : File_Type) return Boolean
     with Global     => null,
          Convention => Ghost;

   function Is_Standard_Writable (File : File_Type) return Boolean is
     (Is_Standard_Output (File) or else Is_Standard_Error (File))
   with Global     => null,
        Convention => Ghost;

   function Is_Standard_File (File : File_Type) return Boolean is
     (Is_Standard_Input (File) or else Is_Standard_Output (File)
          or else Is_Standard_Error (File))
     with Global     => null,
          Convention => Ghost;

   function Is_Open (File : in File_Type) return Boolean
     with Global => null;

   function Mode (File : in File_Type) return File_Mode
     with Global => null,
          Pre    => Is_Open (File);

   --  The function Name behaves differently in SPARK.Text_IO to Ada.Text_IO.
   --  In SPARK.Text_IO instead of raising an exception when the file is
   --  temporary, name returns a  null string ("").
   function Name (File : in File_Type) return String
     with Global => null,
          Pre    => Is_Open (File);

   function Form (File : in File_Type) return String
     with Global => null,
          Pre    => Is_Open (File);

   function Is_Readable (File : File_Type) return Boolean is
     (Is_Open (File) and then Mode (File) = In_File)
     with Global => null;

   function Is_Writable (File : File_Type) return Boolean is
     (Is_Open (File) and then
          (Mode (File) = Out_File or else Mode (File) = Append_File))
     with Global => null;

   --  Cannot be used with Standard Input, Output or Error as these are already
   --  open. The precondition guards against this.
   procedure Create (The_File : in out File_Type;
                     The_Mode : in  File_Mode := Out_File;
                     The_Name : in  String    := "";
                     The_Form : in  String    := "")
     with
       Global => null,
       Pre  => not Is_Open (The_File),
       Post => (if Status (The_File) = Success then
                      Mode (The_File) = The_Mode and
                      Name (The_File) = The_Name and
                      Form (The_File) = The_Form and
                      Is_Open (The_File) and
                      Line_Length (The_File) = 0 and
                      Page_Length (The_File) = 0 and
                      not Is_Standard_File (The_File)
                else
                   not Is_Open (The_File));

   --  Cannot be used with Standard Input, Output or Error as these are already
   --  open.  The precondition guards against this.
   procedure Open (The_File : in out File_Type;
                   The_Mode : in  File_Mode;
                   The_Name : in  String;
                   The_Form : in  String := "")
     with
       Global => null,
       Pre  => not Is_Open (The_File),
       Post => (if Status (The_File) = Success then
                      Mode (The_File) = The_Mode and
                      Name (The_File) = The_Name and
                      Form (The_File) = The_Form and
                      Is_Open (The_File) and
                      Line_Length (The_File) = 0 and
                      Page_Length (The_File) = 0 and
                      not Is_Standard_File (The_File)
                 else
                    not Is_Open (The_File));

   procedure Close (File : in out File_Type)
     with
       Global => null,
       Pre  => Is_Open (File) and not Is_Standard_File (File),
       Post => (if Status (File) = Success then not Is_Open (File));

   procedure Delete (File : in out File_Type)
     with
       Global => null,
       Pre  => Is_Open (File) and not Is_Standard_File (File),
       Post => (if Status (File) = Success then not Is_Open (File));

   procedure Reset (File : in out File_Type; The_Mode : in File_Mode)
     with
       Global => null,
       Pre  => Is_Open (File) and not Is_Standard_File (File),
       Post => (if Status (File) = Success then
                  Mode (File) = The_Mode)
                and (Is_Open (File) and
                     Name (File) = Name (File)'Old and
                     Form (File) = Form (File)'Old and
                     not Is_Standard_File (File));

   procedure Reset (File : in out File_Type)
     with
       Global => null,
       Pre  => Is_Open (File) and then not Is_Standard_File (File),
       Post => Is_Open (File) and then
               Mode (File) = Mode (File)'Old and then
               Name (File) = Name (File)'Old and then
               Form (File) = Form (File)'Old and then
               not Is_Standard_File (File);

   --  The functions Standard_Input, Standard_Output and Standard_Error
   --  have been replaced by variables.

   --  The functions Current_Input, Current_Output and Current_Error are
   --  redundant as the default files are always
   --  Standard_Input, Standard_Output
   --  and Standard_Error.

   --  Buffer control

   procedure Flush (File : in out File_Type)
     with Global => null,
          Pre  => Is_Writable (File),
          Post => Is_Writable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Line_Length (File) = Line_Length (File)'Old and then
                  Page_Length (File) = Page_Length (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Flush
     with Global => (In_Out => Standard_Output),
          Post   => Is_Writable (Standard_Output) and then
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and then
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and then
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and then
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and then
                    Is_Standard_Output (Standard_Output);

   --  Specification of line and page lengths

   procedure Set_Line_Length (File : in out File_Type; To : in Count)
     with Global => null,
          Pre  => Is_Writable (File),
          Post => (if Status (File) = Success then Line_Length (File) = To) and
                  (Is_Writable (File) and
                   Name (File) = Name (File)'Old and
                   Form (File) = Form (File)'Old and
                   Page_Length (File) = Page_Length (File)'Old and
                   Is_Standard_File (File) = Is_Standard_File (File)'Old);

   procedure Set_Line_Length (To : in Count)
     with Global => (In_Out => Standard_Output),
          Post   => (if Status (Standard_Output) = Success then
                    Line_Length (Standard_Output) = To) and then
               (Is_Writable (Standard_Output) and then
                Name (Standard_Output) = Name (Standard_Output)'Old and then
                Form (Standard_Output) = Form (Standard_Output)'Old and then
                Page_Length (Standard_Output) =
                   Page_Length (Standard_Output)'Old and then
                Is_Standard_Output (Standard_Output));


   procedure Set_Page_Length (File : in out File_Type; To : in Count)
     with Global => null,
          Pre  => Is_Writable (File),
          Post => (if Status (File) = Success then Page_Length (File) = To) and
                  (Is_Writable (File) and
                   Name (File) = Name (File)'Old and
                   Form (File) = Form (File)'Old and
                   Line_Length (File) = Line_Length (File)'Old and
                   Is_Standard_File (File) = Is_Standard_File (File)'Old);

   procedure Set_Page_Length (To : in Count)
     with Global => (In_Out => Standard_Output),
          Post   => (if Status (Standard_Output) = Success then
                       Page_Length (Standard_Output) = To) and
                    (Is_Writable (Standard_Output) and
                     Name (Standard_Output) = Name (Standard_Output)'Old and
                     Form (Standard_Output) = Form (Standard_Output)'Old and
                     Line_Length (Standard_Output) =
                        Line_Length (Standard_Output)'Old and
                     Is_Standard_Output (Standard_Output));

   function  Line_Length (File : in File_Type) return Count
     with Global => null,
          Pre    => Is_Writable (File);

   function  Line_Length return Count
     with Global => Standard_Output;

   function  Page_Length (File : in File_Type) return Count
     with Global => null,
          Pre    => Is_Writable (File);

   function  Page_Length return Count
     with Global => Standard_Output;

   --  Column, Line, and Page Control

   procedure New_Line   (File    : in out File_Type;
                         Spacing : in Positive_Count := 1)
     with Global => null,
          Pre  => Is_Writable (File),
          Post => Is_Writable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Line_Length (File) = Line_Length (File)'Old and then
                  Page_Length (File) = Page_Length (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure New_Line   (Spacing : in Positive_Count := 1)
     with Global => (In_Out => Standard_Output),
          Post   => Is_Writable (Standard_Output) and then
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and then
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and then
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and then
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and then
                    Is_Standard_Output (Standard_Output);

   procedure Skip_Line  (File    : in out File_Type;
                         Spacing : in Positive_Count := 1)
     with Global => null,
          Pre  => Is_Readable (File) and then not End_Of_File (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Skip_Line  (Spacing : in Positive_Count := 1)
     with Global => (In_Out => Standard_Input),
          Pre    => Is_Readable (Standard_Input) and then
                    not End_Of_File,
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input);

   function  End_Of_Line (File : in File_Type) return Boolean
     with Global => null,
          Pre    => Is_Readable (File);

   function  End_Of_Line return Boolean
     with Global => Standard_Input;

   procedure New_Page   (File : in out File_Type)
     with Global => null,
          Pre  => Is_Writable (File),
          Post => Is_Writable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Line_Length (File) = Line_Length (File)'Old and then
                  Page_Length (File) = Page_Length (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure New_Page
     with Global => (In_Out => Standard_Output),
          Post   => Is_Writable (Standard_Output) and then
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and then
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and then
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and then
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and then
                    Is_Standard_Output (Standard_Output);

   procedure Skip_Page  (File : in out File_Type)
     with Global => null,
          Pre  => Is_Readable (File) and then not End_Of_File (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Skip_Page
     with Global => (In_Out => Standard_Input),
          Pre    => Is_Readable (Standard_Input) and then
                    not End_Of_File,
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input);

   function  End_Of_Page (File : in File_Type) return Boolean
     with Global => null,
          Pre    => Is_Readable (File);

   function  End_Of_Page return Boolean
     with Global => Standard_Input;

   function  End_Of_File (File : in File_Type) return Boolean
     with Global => null,
          Pre    => Is_Readable (File);

   function  End_Of_File return Boolean
     with Global => Standard_Input,
          Post   => End_Of_File'Result = End_Of_File (Standard_Input);

   procedure Set_Col (File : in out File_Type; To : in Positive_Count)
     with Global => null,
          Pre  => (if Is_Writable (File) and then Line_Length (File) > 0 then
                       To <= Line_Length (File)
                   elsif Is_Readable (File) then not End_Of_File (File)),
          Post => (if Status (File) = Success then
                     Col (File) = (Success, To)) and
                  (Is_Writable (File) = Is_Writable (File)'Old and
                   Is_Readable (File)  = Is_Readable (File)'Old and
                   Name (File) = Name (File)'Old and
                   Form (File) = Form (File)'Old and
                   Is_Standard_File (File) = Is_Standard_File (File)'Old);

   procedure Set_Col (To   : in Positive_Count)
     with Global => (In_Out => Standard_Output),
          Pre    => Is_Writable (Standard_Output) and then
                    (if Line_Length (Standard_Output) > 0 then
                        To <= Line_Length (Standard_Output)),
          Post   => (if Status (Standard_Output) = Success then
                        Col (Standard_Output) = (Success, To)) and
                     Name (Standard_Output) = Name (Standard_Output)'Old and
                     Form (Standard_Output) = Form (Standard_Output)'Old and
                    (Is_Writable (Standard_Output) and
                     Is_Standard_Output (Standard_Output));

   procedure Set_Line (File : in out File_Type; To : in Positive_Count)
     with Global => null,
          Pre  => Is_Writable (File) and then
                    (if Page_Length (File) > 0 then
                       To <= Page_Length (File)
                   elsif Is_Readable (File) then not End_Of_File (File)),
          Post => (if Status (File) = Success then
                     Page (File) = (Success, To)) and
                  (Is_Writable (File) = Is_Writable (File)'Old and
                   Is_Readable (File)  = Is_Readable (File)'Old and
                   Name (File) = Name (File)'Old and
                   Form (File) = Form (File)'Old and
                   Is_Standard_File (File) = Is_Standard_File (File)'Old);

   procedure Set_Line (To   : in Positive_Count)
     with Global => (In_Out => Standard_Output),
          Pre    => Is_Writable (Standard_Output) and then
                    (if Page_Length > 0 then
                        To <= Page_Length (Standard_Output)),
          Post => (if Status (Standard_Output) = Success then
                     Line (Standard_Output) = (Success, To)) and
                  (Is_Writable (Standard_Output) and
                   Name (Standard_Output) = Name (Standard_Output)'Old and
                   Form (Standard_Output) = Form (Standard_Output)'Old and
                   Is_Standard_Output (Standard_Output));

   function Col (File : in File_Type) return Count_Result
   with Global => null,
        Pre    => Is_Open (File);

   function Col  return Count_Result
     with Global => Standard_Output;

   function Line (File : in File_Type) return Count_Result
   with Global => null,
        Pre    => Is_Open (File);

   function Line return Count_Result
     with Global => Standard_Output;

   function Page (File : in File_Type) return Count_Result
   with Global => null,
        Pre    => Is_Open (File);

   function Page return Count_Result
     with Global => Standard_Output;

   --  Character Input-Output

   procedure Get (File : in out File_Type; Item : out Character_Result)
     with Global => null,
          Pre  => Is_Readable (File) and then not End_Of_File (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Get (Item : out Character_Result)
     with Global => (In_Out => Standard_Input),
     Pre    => not End_Of_File or else
                      (Is_Readable (Standard_Input) and then
                          not End_Of_File (Standard_Input)),
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_File (Standard_Input) and then
                    Is_Standard_Input (Standard_Input) and then
                    (if Item.Status = Success then
                        Status (Standard_Input) = Success);

   procedure Put (File : in out File_Type; Item : in Character)
     with Global => null,
          Pre  => Is_Writable (File) and then Status (File) = Success,
          Post => Is_Writable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Line_Length (File) = Line_Length (File)'Old and then
                  Page_Length (File) = Page_Length (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Put (Item : in  Character)
     with Global => (In_Out => Standard_Output),
          Pre    => Status (Standard_Output) = Success,
     Post   => Name (Standard_Output) =
                  Name (Standard_Output)'Old and then
               Form (Standard_Output) =
                  Form (Standard_Output)'Old and then
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and then
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and then
                  Is_Standard_Output (Standard_Output);

   procedure Look_Ahead (File        : in  out File_Type;
                         Item        : out Character_Result;
                         End_Of_Line : out Boolean)
     with Global => null,
          Pre  => Is_Readable (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Look_Ahead (Item        : out Character_Result;
                         End_Of_Line : out Boolean)
     with Global => (In_Out => Standard_Input),
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input);

   procedure Get_Immediate (File      : in out File_Type;
                            Item      :    out Character_Result)
     with Global => null,
          Pre  => Is_Readable (File) and then not End_Of_File (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Get_Immediate (Item      :    out Character_Result)
     with Global => (In_Out => Standard_Input),
          Pre    => Is_Readable (Standard_Input) and then
                    not End_Of_File,
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input);

   procedure Get_Immediate (File      : in out File_Type;
                            Item      :    out Immediate_Result;
                            Available :    out Boolean)
     with Global => null,
          Pre  => Is_Readable (File) and then not End_Of_File (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Get_Immediate (Item      : out Immediate_Result;
                            Available : out Boolean)
     with Global => (In_Out => Standard_Input),
          Pre    => Is_Readable (Standard_Input) and then
                    not End_Of_File,
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input);

   --  String Input-Output

   procedure Get (File          : in out File_Type;
                  Item          : out String)
     with Global => null,
          Pre  => Is_Readable (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) =
                     Is_Standard_File (File)'Old and then
                  (if Status (File) = Success then Item'Length >= 0);

   procedure Get (Item : out String)
     with Global => (In_Out => Standard_Input),
          Pre    => Status (Standard_Input) = Success,
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input) and then
                    (if Status (Standard_Input) = Success then
                        Item'Length >= 0);

   procedure Put (File : in out File_Type; Item : in String)
     with Global => null,
          Pre  => Is_Writable (File) and then Status (File) = Success,
          Post => Is_Writable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Line_Length (File) = Line_Length (File)'Old and then
                  Page_Length (File) = Page_Length (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Put (Item : in  String)
     with Global => (In_Out => Standard_Output),
          Pre    => Status (Standard_Output) = Success,
          Post => Is_Writable (Standard_Output) and then
                  Name (Standard_Output) = Name (Standard_Output)'Old and then
                  Form (Standard_Output) = Form (Standard_Output)'Old and then
                  Line_Length (Standard_Output) =
                     Line_Length (Standard_Output)'Old and then
                  Page_Length (Standard_Output) =
                     Page_Length (Standard_Output)'Old and then
                  Is_Standard_Output (Standard_Output);

   --  Function_Get_Line is not supported as reading the file has an effect
   --  and the file status following a read is updated meaning the file
   --  parameter is in out.
   --  This is not supported in SPARK - functions shall not have side-effects.

   procedure Get_Line (File : in out File_Type;
                       Item : out String;
                       Last : out Natural)
     with Global => null,
          Pre  => Is_Readable (File),
          Post => Is_Readable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Is_Standard_File (File) =
                     Is_Standard_File (File)'Old and then
                  (if Status (File) = Success then
                      Last >= Item'First - 1 and Last <= Item'Last
                   else
                      Last = 0);

   procedure Get_Line (Item : out String; Last : out Natural)
     with Global => (In_Out => Standard_Input),
          Post   => Is_Readable (Standard_Input) and then
                    Name (Standard_Input) = Name (Standard_Input)'Old and then
                    Form (Standard_Input) = Form (Standard_Input)'Old and then
                    Is_Standard_Input (Standard_Input) and then
                    (if Status (Standard_Input) = Success then
                        Last >= Item'First - 1 and Last <= Item'Last
                     else
                        Last = 0);

   procedure Put_Line (File : in out File_Type; Item : in String)
     with Global => null,
          Pre  => Is_Writable (File) and then Status (File) = Success,
          Post => Is_Writable (File) and then
                  Name (File) = Name (File)'Old and then
                  Form (File) = Form (File)'Old and then
                  Line_Length (File) = Line_Length (File)'Old and then
                  Page_Length (File) = Page_Length (File)'Old and then
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;


   procedure Put_Line (Item : in  String)
     with Global => (In_Out => Standard_Output),
          Pre    => Status (Standard_Output) = Success,
          Post   => Is_Writable (Standard_Output) and then
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and then
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and then
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and then
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and then
                    Is_Standard_Output (Standard_Output);

end SPARK.Text_IO;
