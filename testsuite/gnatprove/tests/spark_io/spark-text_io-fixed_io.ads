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

generic
  type Num is delta <>;
package SPARK.Text_IO.Fixed_IO is

   Default_Fore : constant Field := Num'Fore;
   Default_Aft  : constant Field := Num'Aft;
   Default_Exp  : constant Field := 0;

   type Fixed_Result (Status : File_Status := Status_Error) is record
      case Status is
         when Success => Item : Num;
         when others  => null;
      end case;
   end record;

   procedure Get (File  : in out File_Type;
                  Item  : out Fixed_Result;
                  Width : in  Field := 0)
     with Global => null,
          Pre  => Is_Readable (File),
          Post => Is_Readable (File) and
                  Name (File) = Name (File)'Old and
                  Form (File) = Form (File)'Old and
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Get (Item  : out Fixed_Result;
                  Width : in  Field := 0)
     with Global => (In_Out => Standard_Input),
          Post   => Is_Readable (Standard_Input) and
                    Name (Standard_Input) =
                       Name (Standard_Input)'Old and
                    Form (Standard_Input) =
                       Form (Standard_Input)'Old and
                    Is_Standard_Input (Standard_Input);

   procedure Put (File : in out File_Type;
                  Item : in Num;
                  Fore : in Field := Default_Fore;
                  Aft  : in Field := Default_Aft;
                  Exp  : in Field := Default_Exp)
     with Global => null,
          Pre  => Is_Writable (File) and then Status (File) = Success,
          Post => Is_Open (File) and Mode (File) = Mode (File)'Old and
                  Name (File) = Name (File)'Old and
                  Form (File) = Form (File)'Old and
                  Line_Length (File) = Line_Length (File)'Old and
                  Page_Length (File) = Page_Length (File)'Old and
                  Is_Standard_File (File) = Is_Standard_File (File)'Old;

   procedure Put (Item : in Num;
                  Fore : in Field := Default_Fore;
                  Aft  : in Field := Default_Aft;
                  Exp  : in Field := Default_Exp)
     with Global => (In_Out => Standard_Output),
          Pre    => Status (Standard_Output) = Success,
          Post   => Is_Open (Standard_Output) and
                    Mode (Standard_Output) = Out_File and
                    Name (Standard_Output) =
                       Name (Standard_Output)'Old and
                    Form (Standard_Output) =
                       Form (Standard_Output)'Old and
                    Line_Length (Standard_Output) =
                       Line_Length (Standard_Output)'Old and
                    Page_Length (Standard_Output) =
                       Page_Length (Standard_Output)'Old and
                    Is_Standard_Output (Standard_Output);

   procedure Get (From   : in  String;
                  Item   : out Fixed_Result;
                  Last   : out Positive)
     with Global => null;


   procedure Put (To     : out String;
                  Item   : in Num;
                  Aft    : in Field := Default_Aft;
                  Exp    : in Field := Default_Exp)
     with Global => null,
          Pre => To'Length >= 3 + Aft + (if Exp > 0 then Exp + 1 else 0) and
                 To'Length >= Num'Image (Item)'Length;
end SPARK.Text_IO.Fixed_IO;
