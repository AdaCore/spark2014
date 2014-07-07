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

with Ada.Strings.Unbounded;

package SPARK.Text_IO.Unbounded_IO is

   type Unbounded_String_Result
     (Status : File_Status := Status_Error) is record
      case Status is
         when Success =>
            Item : Ada.Strings.Unbounded.Unbounded_String;
         when others =>
            null;
      end case;
   end record;

   procedure Put
      (File : in out File_Type;
       Item : in Ada.Strings.Unbounded.Unbounded_String)
     with Pre  => Is_Writable (File) and then Status (File) = Success,
          Post => Is_Writable (File) and
                  Name (File) = Name (File)'Old and
                  Form (File) = Form (File)'Old and
                  Line_Length (File) = Line_Length (File)'Old and
                  Page_Length (File) = Page_Length (File)'Old and
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Put
     (Item : in Ada.Strings.Unbounded.Unbounded_String)
     with Global => (In_Out => Standard_Output),
          Pre    => Status (Standard_Output) = Success,
          Post   => Is_Writable (Standard_Output) and
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and
                   Is_Standard_File (Standard_Output);

   procedure Put_Line
      (File : in out File_Type;
       Item : in Ada.Strings.Unbounded.Unbounded_String)
     with Pre  => Is_Writable (File) and then Status (File) = Success,
          Post => Is_Writable (File) and
                  Name (File) = Name (File)'Old and
                  Form (File) = Form (File)'Old and
                  Line_Length (File) = Line_Length (File)'Old and
                  Page_Length (File) = Page_Length (File)'Old and
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Put_Line
      (Item : in Ada.Strings.Unbounded.Unbounded_String)
     with Global => (In_Out => Standard_Output),
          Pre    => Status (Standard_Output) = Success,
          Post   => Is_Writable (Standard_Output) and
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and
                    Is_Standard_File (Standard_Output);

   procedure Get_Line
      (File : in out File_Type; Item : out Unbounded_String_Result)
     with Pre  => Is_Readable (File),
          Post => Is_Readable (File) and
                  Name (File) = Name (File)'Old and
                  Form (File) = Form (File)'Old and
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Get_Line
      (Item : out Unbounded_String_Result)
     with Global => (In_Out => Standard_Input),
          Post   => Is_Readable (Standard_Input) and
                    Name (Standard_Input) = Name (Standard_Input)'Old and
                    Form (Standard_Input) = Form (Standard_Input)'Old and
                    Is_Standard_File (Standard_Input);

end SPARK.Text_IO.Unbounded_IO;
