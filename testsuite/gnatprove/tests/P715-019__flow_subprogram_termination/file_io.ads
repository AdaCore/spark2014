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
   SPARK_Mode
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

   function Size (F : File) return Natural;
   --  The size of the file.

   function Index (F : File) return Natural
   with Post => Index'Result <= Size (F);
   --  The position of the last character read.

   procedure Open_Read (Filename : String;
                        F        : out File)
   with Post => Index (F) = 0;
   --  Open the given file for reading.

   procedure Read (F : in out File;
                   R :    out Read_Result)
   with Pre  => not R'Constrained,
        Post => Size (F) = Size (F)'Old and
                Index (F) <= Size (F) and
                (R.Status /= Success or (Index (F) = Index (F)'Old + 1)) and
                (R.Status  = Success or (Index (F) = Index (F)'Old));
   --  Attempt to read a single character. If we were successful, index
   --  increases by 1, otherwise it stays the same. This is written a bit
   --  awkwardly as we can use an if expression here.

   procedure Close (F : in out File);
   --  Close the file.

private
   pragma SPARK_Mode (Off);

   type File is record
      The_File : Ada.Streams.Stream_IO.File_Type;
      Mode     : Ada.Streams.Stream_IO.File_Mode;
      Open     : Boolean                         := False;
      Error    : Boolean                         := False;
      Size     : Natural;
      Index    : Natural;
   end record;

   function Size (F : File) return Natural is (F.Size);

   function Index (F : File) return Natural is (F.Index);

end File_IO;
