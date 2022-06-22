------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                              F I L E _ I O                               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--               Copyright (C) 2016, Altran UK Limited                      --
--                                                                          --
-- sparksmt is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  sparksmt is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  sparksmt;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

private with Ada.Streams.Stream_IO;

--  Safe (but likely slow) file IO that can deal with all exceptions (they
--  are instead encoded in the read result).

package File_IO with
  SPARK_Mode,
  Pure,
  Annotate => (GNATprove, Always_Return)
is

   type File is limited private;

   type Read_Status is (Success, EOF, Error);

   type Read_Result (Status : Read_Status := Error) is record
      case Status is
         when Success =>
            C : Character;
         when EOF | Error =>
            null;
      end case;
   end record;

   procedure Open_Read (Filename : String;
                        F        : out File);
   --  Open the given file for reading.

   procedure Read (F : in out File;
                   R :    out Read_Result)
   with Pre => not R'Constrained;
   --  Attempt to read a single character.

   procedure Close (F : in out File);
   --  Close the file.

private
   pragma SPARK_Mode (Off);

   type File is record
      The_File : Ada.Streams.Stream_IO.File_Type;
      Mode     : Ada.Streams.Stream_IO.File_Mode;
      Open     : Boolean                         := False;
      Error    : Boolean                         := False;
   end record;

end File_IO;
