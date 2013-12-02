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

package body SPARK.Text_IO.Enumeration_IO is

   package Ada_Enum_IO is new Ada.Text_IO.Enumeration_IO (Enum);

   procedure Get (File : in out File_Type;
                  Item : out Enum_Result) is
      E : Enum;
   begin
      case File.Sort is
         when Std_Out | Std_Error =>
            Item := (Status => Mode_Error);
            File.Status := Mode_Error;
         when Std_In =>
            Ada_Enum_IO.Get (Ada.Text_IO.Standard_Input, E);
            Item := (Status => Success, Item => E);
            File.Status := Success;
         when A_File =>
            Ada_Enum_IO.Get (File.File, E);
            Item := (Status => Success, Item => E);
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
      when Ada.Text_IO.Data_Error =>
         Item := (Status => Data_Error);
         File.Status := Data_Error;
   end Get;

   procedure Get (Item : out Enum_Result) is
      E : Enum;
   begin
      Ada_Enum_IO.Get (Ada.Text_IO.Standard_Input, E);
      Item := (Status => Success, Item => E);
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
      when Ada.Text_IO.Data_Error =>
         Item := (Status => Data_Error);
         Standard_Input.Status := Data_Error;
   end Get;

   procedure Put (File  : in out File_Type;
                  Item  : in Enum;
                  Width : in Field    := Default_Width;
                  Set   : in Type_Set := Default_Setting) is
   begin
      case File.Sort is
         when Std_In =>
            File.Status := Mode_Error;
         when Std_Out =>
            Ada_Enum_IO.Put (Ada.Text_IO.Standard_Output,
                             Item, Width, Ada.Text_IO.Type_Set (Set));
            File.Status := Success;
         when Std_Error =>
            Ada_Enum_IO.Put (Ada.Text_IO.Standard_Error,
                             Item, Width, Ada.Text_IO.Type_Set (Set));
            File.Status := Success;
         when A_File =>
            Ada_Enum_IO.Put (File.File,
                             Item, Width, Ada.Text_IO.Type_Set (Set));
            File.Status := Success;
      end case;
   exception
      when Ada.Text_IO.Status_Error => File.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   => File.Status := Mode_Error;
      when Ada.Text_IO.Device_Error => File.Status := Device_Error;
   end Put;

   procedure Put (Item  : in Enum;
                  Width : in Field    := Default_Width;
                  Set   : in Type_Set := Default_Setting) is
   begin
      Ada_Enum_IO.Put (Ada.Text_IO.Standard_Output,
                       Item, Width, Ada.Text_IO.Type_Set (Set));
      Standard_Output.Status := Success;
   exception
      when Ada.Text_IO.Status_Error =>
         Standard_Output.Status := Status_Error;
      when Ada.Text_IO.Mode_Error   =>
         Standard_Output.Status := Mode_Error;
      when Ada.Text_IO.Device_Error =>
         Standard_Output.Status := Device_Error;
   end Put;

   procedure Get (From   : in  String;
                  Item   : out Enum_Result;
                  Last   : out Positive) is
      E : Enum;
   begin
      Ada_Enum_IO.Get (From, E, Last);
      Item := (Status => Success, Item => E);
   exception
      when Ada.Text_IO.Data_Error =>
         Item := (Status => Data_Error);
         Last := 1;
   end Get;


   procedure Put (To     : out String;
                  Item   : in  Enum;
                  Set    : in  Type_Set := Default_Setting) is
   begin
      Ada_Enum_IO.Put (To, Item, Ada.Text_IO.Type_Set (Set));
   end Put;
end SPARK.Text_IO.Enumeration_IO;
