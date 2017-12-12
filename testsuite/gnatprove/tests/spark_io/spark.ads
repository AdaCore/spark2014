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

with Ada.Text_IO;

package SPARK is

   --  For each operation on a file a file status is recorded in the File_Type.
   --
   --  The identifiers of the File_Status enumeration correspond to the
   --  Exception identifiers of IO_Exceptions that may be propagated by the Ada
   --  file handling subprograms.
   --
   --  Instead of raising an exception the SPARK file handling subprograms
   --  record (in the File_Type) the status corresponding to the exception.
   --  If no exception would have been raised the status is Success.

   type File_Status is (Unopened,
                        Success,
                        Std_File_Error,    -- Attempt to open a Standard File
                        Status_Error,
                        Mode_Error,
                        Name_Error,
                        Use_Error,
                        Device_Error,
                        End_Error,
                        Data_Error,
                        Layout_Error);

   type Text_IO_File_Type is limited private with Default_Initial_Condition;

private
   pragma SPARK_Mode (Off);
   type Text_IO_File_Sort is (Std_In, Std_Out, Std_Error, A_File);
   subtype Std_Files is Text_IO_File_Sort range Std_In .. Std_Error;

   type Text_IO_File_Type is record
      Status : File_Status       := Unopened;
      Sort   : Text_IO_File_Sort := A_File;
      File   : Ada.Text_IO.File_Type;
   end record;

end SPARK;
