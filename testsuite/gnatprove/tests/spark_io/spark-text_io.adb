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

pragma SPARK_Mode (Off);

with Ada.Exceptions;

package body SPARK.Text_IO is

   function Status (File : File_Type) return File_Status is
     (File_Status (File.Status));

   function Is_Standard_Input (File : File_Type) return Boolean is
      (File.Sort = Std_In);

   function Is_Standard_Output (File : File_Type) return Boolean is
      (File.Sort = Std_Out);

   function Is_Standard_Error (File : File_Type) return Boolean is
      (File.Sort in Std_Error);

   function  Mode   (File : in File_Type) return File_Mode is
     (case File.Sort is
         when Std_In => In_File,
         when Std_Out | Std_Error => Out_File,
         when A_File => File_Mode (Ada.Text_IO.Mode (File.File)));

   function  Name   (File : in File_Type) return String is
   begin
      return (case File.Sort is
         when Std_In    => Ada.Text_IO.Name (Ada.Text_IO.Standard_Input),
         when Std_Out   => Ada.Text_IO.Name (Ada.Text_IO.Standard_Output),
         when Std_Error => Ada.Text_IO.Name (Ada.Text_IO.Standard_Error),
         when A_File => Ada.Text_IO.Name (File.File));
   exception
      when Ada.Text_IO.Use_Error |
           Ada.Text_IO.Device_Error => return "";
   end Name;

   function  Form   (File : in File_Type) return String is
     (case File.Sort is
         when Std_In => Ada.Text_IO.Form (Ada.Text_IO.Standard_Input),
         when Std_Out => Ada.Text_IO.Form (Ada.Text_IO.Standard_Output),
         when Std_Error => Ada.Text_IO.Form (Ada.Text_IO.Standard_Error),
         when A_File => Ada.Text_IO.Form (File.File));

   function  Is_Open (File : in File_Type) return Boolean is
     (File.Status /= Unopened and then
        (case File.Sort is
            when Std_Files => True,
            when A_File => Ada.Text_IO.Is_Open (File.File)));

   function Get_Standard_File (Sort : Std_Files)
                               return Ada.Text_IO.File_Type is
     (case Sort is
         when Std_In => Ada.Text_IO.Standard_Input,
         when Std_Out => Ada.Text_IO.Standard_Output,
         when Std_Error => Ada.Text_IO.Standard_Error);

   procedure Create (The_File : in out File_Type;
                     The_Mode : in File_Mode := Out_File;
                     The_Name : in String    := "";
                     The_Form : in String    := "")
   is
   begin
      Ada.Text_IO.Create (The_File.File,
                          Ada.Text_IO.File_Mode (The_Mode),
                          The_Name,
                          The_Form);
      The_File.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => The_File.Status := Status_Error;
      when Ada.Text_IO.Name_Error   => The_File.Status := Name_Error;
      when Ada.Text_IO.Use_Error    => The_File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => The_File.Status := Device_Error;
   end Create;

   procedure Open (The_File : in out File_Type;
                   The_Mode : in File_Mode;
                   The_Name : in String;
                   The_Form : in String := "")
   is
   begin
      Ada.Text_IO.Open (The_File.File,
                        Ada.Text_IO.File_Mode (The_Mode),
                        The_Name,
                        The_Form);
      The_File.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => The_File.Status := Status_Error;
      when Ada.Text_IO.Name_Error   => The_File.Status := Name_Error;
      when Ada.Text_IO.Use_Error    => The_File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => The_File.Status := Device_Error;
   end Open;

   procedure Close  (File : in out File_Type) is
   begin
      case File.Sort is
         when Std_Files => File.Status := Std_File_Error;
         when A_File =>
            Ada.Text_IO.Close (File.File);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Close;


   procedure Delete (File : in out File_Type) is
   begin
      case File.Sort is
         when Std_Files => File.Status := Std_File_Error;
         when A_File =>
            Ada.Text_IO.Delete (File.File);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Use_Error    => File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Delete;

   procedure Reset  (File : in out File_Type; The_Mode : in File_Mode) is
   begin
      case File.Sort is
         when Std_Files => File.Status := Std_File_Error;
         when A_File =>
            Ada.Text_IO.Reset (File.File, Ada.Text_IO.File_Mode (The_Mode));
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Use_Error    => File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Reset;

   procedure Reset  (File : in out File_Type) is
   begin
      case File.Sort is
         when Std_Files => File.Status := Std_File_Error;
         when A_File =>
            Ada.Text_IO.Reset (File.File);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Use_Error    => File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Reset;

   procedure Flush (File : in out File_Type) is
   begin
      case File.Sort is
         when Std_In => File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Flush (Ada.Text_IO.Standard_Output);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Flush (Ada.Text_IO.Standard_Error);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Flush (File.File);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Flush;

   procedure Flush is
   begin
      Ada.Text_IO.Flush (Ada.Text_IO.Standard_Output);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Flush;

   procedure Set_Line_Length (File : in out File_Type; To : in Count) is
   begin
      case File.Sort is
         when Std_In => File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Set_Line_Length (Ada.Text_IO.Standard_Output,
                                         Ada.Text_IO.Count (To));
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Set_Line_Length (Ada.Text_IO.Standard_Error,
                                         Ada.Text_IO.Count (To));
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Set_Line_Length (File.File, Ada.Text_IO.Count (To));
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Use_Error    => File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Set_Line_Length;

   procedure Set_Line_Length (To : in Count) is
   begin
      Ada.Text_IO.Set_Line_Length (Ada.Text_IO.Standard_Output,
                                   Ada.Text_IO.Count (To));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Use_Error    => Standard_Output.Status := Use_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Set_Line_Length;

   procedure Set_Page_Length (File : in out File_Type; To : in Count) is
   begin
      case File.Sort is
         when Std_In => File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Set_Page_Length (Ada.Text_IO.Standard_Output,
                                         Ada.Text_IO.Count (To));
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Set_Page_Length (Ada.Text_IO.Standard_Error,
                                         Ada.Text_IO.Count (To));
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Set_Page_Length (File.File, Ada.Text_IO.Count (To));
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Use_Error    => File.Status := Use_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Set_Page_Length;


   procedure Set_Page_Length (To : in Count) is
   begin
      Ada.Text_IO.Set_Page_Length (Ada.Text_IO.Standard_Output,
                                   Ada.Text_IO.Count (To));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Use_Error    => Standard_Output.Status := Use_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Set_Page_Length;

   function  Line_Length (File : in File_Type) return Count is
     (case File.Sort is
         when Std_Out =>
            Count (Ada.Text_IO.Line_Length (Ada.Text_IO.Standard_Output)),
         when Std_Error =>
            Count (Ada.Text_IO.Line_Length (Ada.Text_IO.Standard_Error)),
         when others =>  -- This is ok because of the precondition
            Count (Ada.Text_IO.Line_Length (File.File)));

   function  Line_Length return Count is
     (Count (Ada.Text_IO.Line_Length (Ada.Text_IO.Standard_Output)));

   function  Page_Length (File : in File_Type) return Count is
     (case File.Sort is
         when Std_Out =>
            Count (Ada.Text_IO.Page_Length (Ada.Text_IO.Standard_Output)),
         when Std_Error =>
            Count (Ada.Text_IO.Page_Length (Ada.Text_IO.Standard_Error)),
         when others =>  -- This is ok because of the precondition
            Count (Ada.Text_IO.Page_Length (File.File)));

   function  Page_Length return Count is
     (Count (Ada.Text_IO.Page_Length (Ada.Text_IO.Standard_Output)));

   procedure New_Line   (File    : in out File_Type;
                         Spacing : in Positive_Count := 1) is
   begin
      case File.Sort is
         when Std_In => File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.New_Line (Ada.Text_IO.Standard_Output,
                                  Ada.Text_IO.Count (Spacing));
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.New_Line (Ada.Text_IO.Standard_Error,
                                  Ada.Text_IO.Count (Spacing));
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.New_Line (File.File, Ada.Text_IO.Count (Spacing));
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end New_Line;

   procedure New_Line   (Spacing : in Positive_Count := 1) is
   begin
      Ada.Text_IO.New_Line (Ada.Text_IO.Standard_Output,
                            Ada.Text_IO.Count (Spacing));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end New_Line;

   procedure Skip_Line  (File    : in out File_Type;
                         Spacing : in Positive_Count := 1) is
   begin
      case File.Sort is
         when Std_Out | Std_Error => File.Status := Mode_Error;
         when Std_In =>
            Ada.Text_IO.Skip_Line (Ada.Text_IO.Standard_Input,
                                   Ada.Text_IO.Positive_Count (Spacing));
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Skip_Line (File.File,
                                   Ada.Text_IO.Positive_Count (Spacing));
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
      when Ada.Text_IO.End_Error    => File.Status := End_Error;
   end Skip_Line;

   procedure Skip_Line  (Spacing : in Positive_Count := 1) is
   begin
      Ada.Text_IO.Skip_Line (Ada.Text_IO.Standard_Input,
                             Ada.Text_IO.Positive_Count (Spacing));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Input.Status := Device_Error;
      when Ada.Text_IO.End_Error    => Standard_Input.Status := End_Error;
   end Skip_Line;

   function  End_Of_Line (File : in File_Type) return Boolean is
     (case File.Sort is
         when Std_In => Ada.Text_IO.End_Of_Line (Ada.Text_IO.Standard_Input),
         when others => -- Ok because of precondition
            Ada.Text_IO.End_Of_Line (File.File));

   function  End_Of_Line return Boolean is
      (Ada.Text_IO.End_Of_Line (Ada.Text_IO.Standard_Input));

   procedure New_Page   (File : in out File_Type) is
   begin
      case File.Sort is
         when Std_In => File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.New_Page (Ada.Text_IO.Standard_Output);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.New_Page (Ada.Text_IO.Standard_Error);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.New_Page (File.File);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end New_Page;

   procedure New_Page is
   begin
      Ada.Text_IO.New_Page (Ada.Text_IO.Standard_Output);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end New_Page;


   procedure Skip_Page  (File : in out File_Type) is
   begin
      case File.Sort is
         when Std_Out | Std_Error => File.Status := Mode_Error;
         when Std_In =>
            Ada.Text_IO.Skip_Page (Ada.Text_IO.Standard_Input);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Skip_Page (File.File);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
      when Ada.Text_IO.End_Error    => File.Status := End_Error;
   end Skip_Page;

   procedure Skip_Page is
   begin
      Ada.Text_IO.Skip_Page (Ada.Text_IO.Standard_Input);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Input.Status := Device_Error;
      when Ada.Text_IO.End_Error    => Standard_Input.Status := End_Error;
   end Skip_Page;

   function  End_Of_Page (File : in File_Type) return Boolean is
     (case File.Sort is
         when Std_In => Ada.Text_IO.End_Of_Line (Ada.Text_IO.Standard_Input),
         when others => -- Ok because of precondition
            Ada.Text_IO.End_Of_Line (File.File));

   function  End_Of_Page return Boolean is
      (Ada.Text_IO.End_Of_Page (Ada.Text_IO.Standard_Input));

   function  End_Of_File (File : in File_Type) return Boolean is
     (case File.Sort is
         when Std_In => Ada.Text_IO.End_Of_File (Ada.Text_IO.Standard_Input),
         when others => -- Ok because of precondition
            Ada.Text_IO.End_Of_File (File.File));


   function  End_Of_File return Boolean is
      (Ada.Text_IO.End_Of_File (Ada.Text_IO.Standard_Input));

   procedure Set_Col (File : in out File_Type; To : in Positive_Count) is
   begin
      case File.Sort is
         when Std_In =>
            Ada.Text_IO.Set_Col (Ada.Text_IO.Standard_Input,
                                 Ada.Text_IO.Positive_Count (To));
         when Std_Out =>
            Ada.Text_IO.Set_Col (Ada.Text_IO.Standard_Output,
                                 Ada.Text_IO.Positive_Count (To));
         when Std_Error =>
            Ada.Text_IO.Set_Col (Ada.Text_IO.Standard_Error,
                                 Ada.Text_IO.Positive_Count (To));
         when A_File =>
            Ada.Text_IO.Set_Col (File.File,
                                 Ada.Text_IO.Positive_Count (To));
      end case;
      File.Status := Success;
   exception
         when Ada.Text_IO.Status_Error => File.Status := Status_Error;
         when Ada.Text_IO.Device_Error => File.Status := Device_Error;
         when Ada.Text_IO.End_Error    => File.Status := End_Error;
         when Ada.Text_IO.Layout_Error => File.Status := Layout_Error;
   end Set_Col;

   procedure Set_Col (To   : in Positive_Count) is
   begin
      Ada.Text_IO.Set_Col (Ada.Text_IO.Standard_Output,
                           Ada.Text_IO.Positive_Count (To));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Device_Error =>
         Standard_Output.Status := Device_Error;
      when Ada.Text_IO.Layout_Error =>
         Standard_Output.Status := Layout_Error;
   end Set_Col;

   procedure Set_Line (File : in out File_Type; To : in Positive_Count) is
   begin
      case File.Sort is
         when Std_In =>
            Ada.Text_IO.Set_Line (Ada.Text_IO.Standard_Input,
                                 Ada.Text_IO.Positive_Count (To));
         when Std_Out =>
            Ada.Text_IO.Set_Line (Ada.Text_IO.Standard_Output,
                                  Ada.Text_IO.Positive_Count (To));
         when Std_Error =>
            Ada.Text_IO.Set_Line (Ada.Text_IO.Standard_Error,
                                  Ada.Text_IO.Positive_Count (To));
         when A_File =>
            Ada.Text_IO.Set_Line (File.File,
                                  Ada.Text_IO.Positive_Count (To));
      end case;
      File.Status := Success;
   exception
         when Ada.Text_IO.Status_Error => File.Status := Status_Error;
         when Ada.Text_IO.Device_Error => File.Status := Device_Error;
         when Ada.Text_IO.End_Error    => File.Status := End_Error;
         when Ada.Text_IO.Layout_Error => File.Status := Layout_Error;
   end Set_Line;

   procedure Set_Line (To   : in Positive_Count) is
   begin
      Ada.Text_IO.Set_Line (Ada.Text_IO.Standard_Output,
                            Ada.Text_IO.Positive_Count (To));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Device_Error =>
         Standard_Output.Status := Device_Error;
      when Ada.Text_IO.Layout_Error =>
         Standard_Output.Status := Layout_Error;
   end Set_Line;

   function Col (File : in File_Type) return Count_Result is
   begin
      return (case File.Sort is
         when Std_In    => (Success,
                            Positive_Count
                              (Ada.Text_IO.Col (Ada.Text_IO.Standard_Input))),
         when Std_Out   => (Success,
                            Positive_Count
                              (Ada.Text_IO.Col (Ada.Text_IO.Standard_Output))),
         when Std_Error => (Success,
                            Positive_Count
                              (Ada.Text_IO.Col (Ada.Text_IO.Standard_Error))),
         when A_File    => (Success,
                            Positive_Count (Ada.Text_IO.Col (File.File))));
   exception
         when Ada.Text_IO.Status_Error => return (Status => Status_Error);
         when Ada.Text_IO.Device_Error => return (Status => Device_Error);
         when Ada.Text_IO.Layout_Error => return (Status => Layout_Error);
   end Col;

   function Col  return Count_Result is
   begin
      return (Success,
              Positive_Count (Ada.Text_IO.Col (Ada.Text_IO.Standard_Output)));
   exception
         when Ada.Text_IO.Status_Error => return (Status => Status_Error);
         when Ada.Text_IO.Device_Error => return (Status => Device_Error);
         when Ada.Text_IO.Layout_Error => return (Status => Layout_Error);
   end Col;


   function Line (File : in File_Type) return Count_Result is
   begin
      return
        (case File.Sort is
            when Std_In    => (Success,
                               Positive_Count
                                 (Ada.Text_IO.Line
                                    (Ada.Text_IO.Standard_Input))),
            when Std_Out   => (Success,
                               Positive_Count
                                 (Ada.Text_IO.Line
                                    (Ada.Text_IO.Standard_Output))),
            when Std_Error => (Success,
                               Positive_Count
                                 (Ada.Text_IO.Line
                                    (Ada.Text_IO.Standard_Error))),
            when A_File    => (Success,
                               Positive_Count
                                 (Ada.Text_IO.Line (File.File))));
   exception
         when Ada.Text_IO.Status_Error => return (Status => Status_Error);
         when Ada.Text_IO.Device_Error => return (Status => Device_Error);
         when Ada.Text_IO.Layout_Error => return (Status => Layout_Error);
   end Line;

   function Line return Count_Result is
   begin
      return (Success,
              Positive_Count (Ada.Text_IO.Line (Ada.Text_IO.Standard_Output)));
   exception
         when Ada.Text_IO.Status_Error => return (Status => Status_Error);
         when Ada.Text_IO.Device_Error => return (Status => Device_Error);
         when Ada.Text_IO.Layout_Error => return (Status => Layout_Error);
   end Line;

   function Page (File : in File_Type) return Count_Result is
   begin
      return (case File.Sort is
         when Std_In    => (Success,
                            Positive_Count
                              (Ada.Text_IO.Page
                                 (Ada.Text_IO.Standard_Input))),
         when Std_Out   => (Success,
                            Positive_Count
                              (Ada.Text_IO.Page
                                 (Ada.Text_IO.Standard_Output))),
         when Std_Error => (Success,
                            Positive_Count
                              (Ada.Text_IO.Page
                                 (Ada.Text_IO.Standard_Error))),
         when A_File    => (Success,
                            Positive_Count
                              (Ada.Text_IO.Page (File.File))));
   exception
         when Ada.Text_IO.Status_Error => return (Status => Status_Error);
         when Ada.Text_IO.Device_Error => return (Status => Device_Error);
         when Ada.Text_IO.Layout_Error => return (Status => Layout_Error);
   end Page;

   function Page return Count_Result is
   begin
      return (Success,
              Positive_Count (Ada.Text_IO.Page (Ada.Text_IO.Standard_Output)));
   exception
         when Ada.Text_IO.Status_Error => return (Status => Status_Error);
         when Ada.Text_IO.Device_Error => return (Status => Device_Error);
         when Ada.Text_IO.Layout_Error => return (Status => Layout_Error);
   end Page;

   procedure Get (File : in out File_Type; Item : out Character_Result) is
      Ch : Character;
   begin
      case File.Sort is
         when Std_Out | Std_Error =>
            Item := (Status => Mode_Error);
            File.Status := Mode_Error;
         when Std_In =>
            Ada.Text_IO.Get (Ada.Text_IO.Standard_Input, Ch);
            Item := (Success, Ch);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Get (File.File, Ch);
            Item := (Success, Ch);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error);
         File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error);
         File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error);
         File.Status := Device_Error;
      when Ada.Text_IO.End_Error =>
         Item := (Status => End_Error);
         File.Status := End_Error;
   end Get;

   procedure Get (Item : out Character_Result) is
      Ch : Character;
   begin
      Ada.Text_IO.Get (Ada.Text_IO.Standard_Input, Ch);
      Item := (Success, Ch);
      Standard_Input.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error);
         Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error);
         Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error);
         Standard_Input.Status := Device_Error;
      when Ada.Text_IO.End_Error =>
         Item := (Status => End_Error);
         Standard_Input.Status := End_Error;
   end Get;

   procedure Put (File : in out File_Type; Item : in Character) is
   begin
      case File.Sort is
         when Std_In =>
            File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Put (Ada.Text_IO.Standard_Output, Item);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Put (Ada.Text_IO.Standard_Error, Item);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Put (File.File, Item);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Put;



   procedure Put (Item : in  Character) is
   begin
      Ada.Text_IO.Put (Ada.Text_IO.Standard_Output, Item);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Put;

   procedure Look_Ahead (File        : in  out File_Type;
                         Item        : out Character_Result;
                         End_Of_Line : out Boolean) is
      Ch : Character;
   begin
      case File.Sort is
         when Std_Out | Std_Error =>
            Item := (Status => Mode_Error);
            File.Status := Mode_Error;
         when Std_In =>
            Ada.Text_IO.Look_Ahead (Ada.Text_IO.Standard_Input,
                                    Ch, End_Of_Line);
            if not End_Of_Line then
               Item := (Success, Ch);
            else
               Item := (Status => End_Error);
            end if;
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Look_Ahead (File.File, Ch, End_Of_Line);
            if not End_Of_Line then
               Item := (Success, Ch);
            else
               Item := (Status => End_Error);
            end if;
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error);
         File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error);
         File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error);
         File.Status := Device_Error;
   end Look_Ahead;

   procedure Look_Ahead (Item        : out Character_Result;
                         End_Of_Line : out Boolean) is
      Ch : Character;
   begin
      Ada.Text_IO.Look_Ahead (Ada.Text_IO.Standard_Input, Ch, End_Of_Line);
      if not End_Of_Line then
         Item := (Success, Ch);
      else
         Item := (Status => End_Error);
      end if;
      Standard_Input.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error);
         Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error);
         Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error);
         Standard_Input.Status := Device_Error;
   end Look_Ahead;

   procedure Get_Immediate (File      : in out File_Type;
                           Item      :    out Character_Result) is
      Ch : Character;
   begin
      case File.Sort is
         when Std_Out | Std_Error =>
            Item := (Status => Mode_Error);
            File.Status := Mode_Error;
         when Std_In =>
            Ada.Text_IO.Get_Immediate (Ada.Text_IO.Standard_Input, Ch);
            Item := (Success, Ch);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Get_Immediate (File.File, Ch);
            Item := (Success, Ch);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error);
         File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error);
         File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error);
         File.Status := Device_Error;
      when Ada.Text_IO.End_Error   =>
         Item := (Status => End_Error);
         File.Status := End_Error;
   end Get_Immediate;

   procedure Get_Immediate (Item      :    out Character_Result) is
      Ch : Character;
   begin
      Ada.Text_IO.Get_Immediate (Ada.Text_IO.Standard_Input, Ch);
      Item := (Success, Ch);
      Standard_Input.Status  := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error);
         Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error);
         Standard_Input.Status  := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error);
         Standard_Input.Status  := Device_Error;
      when Ada.Text_IO.End_Error   =>
         Item := (Status => End_Error);
         Standard_Input.Status  := End_Error;
   end Get_Immediate;

   procedure Get_Immediate (File      : in out File_Type;
                           Item      :    out Immediate_Result;
                           Available :    out Boolean) is
      Ch : Character;
   begin
      case File.Sort is
         when Std_Out | Std_Error =>
            Item := (Status => Mode_Error, Available => False);
            File.Status := Std_File_Error;
         when Std_In =>
            Ada.Text_IO.Get_Immediate (Ada.Text_IO.Standard_Input,
                                       Ch, Available);
            if Available then
               Item := (Status => Success, Available => True, Item => Ch);
            else
               Item := (Status => Success, Available => False);
            end if;
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Get_Immediate (File.File, Ch, Available);
            if Available then
               Item := (Status => Success, Available => True, Item => Ch);
            else
               Item := (Status => Success, Available => False);
            end if;
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error, Available => False);
         File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error, Available => False);
         File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error, Available => False);
         File.Status := Device_Error;
      when Ada.Text_IO.End_Error   =>
         Item := (Status => End_Error, Available => False);
         File.Status := End_Error;
   end Get_Immediate;

   procedure Get_Immediate (Item      : out Immediate_Result;
                            Available : out Boolean) is
      Ch : Character;
   begin
      Ada.Text_IO.Get_Immediate (Ada.Text_IO.Standard_Input, Ch, Available);
      if Available then
         Item := (Status => Success, Available => True, Item => Ch);
      else
         Item := (Status => Success, Available => False);
      end if;
      Standard_Input.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Item := (Status => Status_Error, Available => False);
         Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Item := (Status => Mode_Error, Available => False);
         Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Item := (Status => Device_Error, Available => False);
         Standard_Input.Status := Device_Error;
      when Ada.Text_IO.End_Error   =>
         Item := (Status => End_Error, Available => False);
         Standard_Input.Status := End_Error;
   end Get_Immediate;

   procedure Get (File          : in out File_Type;
                  Item          : out String) is
   begin
      if File.Sort = Std_In then
         Ada.Text_IO.Get (Ada.Text_IO.Standard_Input, Item);
      else
         Ada.Text_IO.Get (File.File, Item);
      end if;
      File.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         File.Status := Device_Error;
      when Ada.Text_IO.End_Error =>
         File.Status := End_Error;
   end Get;

   procedure Get (Item : out String) is
   begin
      Ada.Text_IO.Get (Ada.Text_IO.Standard_Input, Item);
      Standard_Input.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Standard_Input.Status := Device_Error;
      when Ada.Text_IO.End_Error =>
         Standard_Input.Status := End_Error;
   end Get;

   procedure Put (File : in out File_Type; Item : in String) is
   begin
      case File.Sort is
         when Std_In =>
            File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Put (Ada.Text_IO.Standard_Output, Item);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Put (Ada.Text_IO.Standard_Error, Item);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Put (File.File, Item);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Put;

   procedure Put (Item : in  String) is
   begin
      Ada.Text_IO.Put (Ada.Text_IO.Standard_Output, Item);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Put;

   procedure Get_Line (File : in out File_Type;
                       Item : out String;
                       Last : out Natural) is
   begin
      if File.Sort = Std_In then
         Ada.Text_IO.Get_Line (Ada.Text_IO.Standard_Input, Item, Last);
      else
         Ada.Text_IO.Get_Line (File.File, Item, Last);
      end if;
      File.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Last := 0;
         File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Last := 0;
         File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Last := 0;
         File.Status := Device_Error;
      when Ada.Text_IO.End_Error =>
         Last := 0;
         File.Status := End_Error;
   end Get_Line;


   procedure Get_Line (Item : out String; Last : out Natural) is
   begin
      Ada.Text_IO.Get_Line (Ada.Text_IO.Standard_Input, Item, Last);
      Standard_Input.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Last := 0;
         Standard_Input.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Last := 0;
         Standard_Input.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Last := 0;
         Standard_Input.Status := Device_Error;
      when Ada.Text_IO.End_Error =>
         Last := 0;
         Standard_Input.Status := End_Error;
   end Get_Line;

   procedure Put_Line (File : in out File_Type; Item : in String) is
   begin
      case File.Sort is
         when Std_In =>
            File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Output, Item);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Item);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Put_Line (File.File, Item);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Put_Line;

   procedure Put_Line (Item : in  String) is
   begin
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Output, Item);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Put_Line;

begin
   --  Initialize the standard files
   pragma Warnings (Off);
   Standard_Input.Status  := Success;
   Standard_Input.Sort    := Std_In;
   Standard_Output.Status := Success;
   Standard_Output.Sort   := Std_Out;
   Standard_Error.Status  := Success;
   Standard_Error.Sort    := Std_Error;
   pragma Warnings (On);

end SPARK.Text_IO;
