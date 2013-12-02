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

with Ada.Text_IO.Unbounded_IO;

package body SPARK.Text_IO.Unbounded_IO is

   procedure Put
      (File : in out File_Type;
       Item : in Ada.Strings.Unbounded.Unbounded_String) is
   begin
      case File.Sort is
         when Std_In =>
            File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Unbounded_IO.Put (Ada.Text_IO.Standard_Output, Item);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Unbounded_IO.Put (Ada.Text_IO.Standard_Error, Item);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Unbounded_IO.Put (File.File, Item);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Put;


   procedure Put
     (Item : in Ada.Strings.Unbounded.Unbounded_String) is
   begin
      Ada.Text_IO.Unbounded_IO.Put (Ada.Text_IO.Standard_Output, Item);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Put;

   procedure Put_Line
      (File : in out File_Type;
       Item : in Ada.Strings.Unbounded.Unbounded_String) is
   begin
      case File.Sort is
         when Std_In =>
            File.Status := Mode_Error;
         when Std_Out =>
            Ada.Text_IO.Unbounded_IO.Put_Line
              (Ada.Text_IO.Standard_Output, Item);
            File.Status := Success;
         when Std_Error =>
            Ada.Text_IO.Unbounded_IO.Put_Line
              (Ada.Text_IO.Standard_Error, Item);
            File.Status := Success;
         when A_File =>
            Ada.Text_IO.Unbounded_IO.Put_Line (File.File, Item);
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Put_Line;


   procedure Put_Line
      (Item : in Ada.Strings.Unbounded.Unbounded_String) is
   begin
      Ada.Text_IO.Unbounded_IO.Put_Line (Ada.Text_IO.Standard_Output, Item);
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error => Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => Standard_Output.Status := Device_Error;
   end Put_Line;

   procedure Get_Line
      (File : in out File_Type; Item : out Unbounded_String_Result) is
   begin
      case File.Sort is
         when Std_Out | Std_Error =>
            Item := (Status => Mode_Error);
            File.Status := Mode_Error;
         when Std_In =>
            Item := (Status => Success,
                     Item   => Ada.Text_IO.Unbounded_IO.Get_Line
                       (Ada.Text_IO.Standard_Input));
         when A_File =>
            Item := (Status => Success,
                     Item   => Ada.Text_IO.Unbounded_IO.Get_Line (File.File));
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
   end Get_Line;


   procedure Get_Line
      (Item : out Unbounded_String_Result) is
   begin
      Item := (Status => Success,
               Item   => Ada.Text_IO.Unbounded_IO.Get_Line
                 (Ada.Text_IO.Standard_Input));
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
   end Get_Line;


end SPARK.Text_IO.Unbounded_IO;
