------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Floppy
--
-- Implementation Notes:
--    Uses WIN32 so is not SPARK.
--
------------------------------------------------------------------

with Ada.Text_IO;
with System;
with Interfaces.C;

use type System.Address;
use type Interfaces.C.Size_T;

package body Floppy
  with SPARK_Mode => Off
is

   OFS_MAXPATHNAME : constant := 4096;
   subtype FilePathNameT is
     Interfaces.C.Char_Array( 0 .. OFS_MAXPATHNAME + 1);

   subtype FileNameStringT is String (1 .. 256);

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   CurrentFile : File.T := File.NullFile;
   WrittenFile : File.T := File.NullFile;

   TempDir : constant String := "Temp";
   FloppyDrive : String( 1 .. 2) := "A:";
   CurrentName : String := "current.txt";
   WrittenName : String := "written.log";


   ------------------------------------------------------------------
   -- FileAndPathName
   --
   -- Description:
   --    Prepends a path to a file name.
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function FilePathAndName(Path : in String;
                            Name : in String) return Interfaces.C.Char_Array
   is
      FullName : String := Path & "\" & Name;
   begin
      return Interfaces.C.To_C(FullName);
   end FilePathAndName;

   ------------------------------------------------------------------
   -- IsPresent
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function IsPresent return Boolean is (True);

   ------------------------------------------------------------------
   -- Write
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Write (TheFile : in File.T)
   is
   begin
      null;
   end Write;

   ------------------------------------------------------------------
   -- Read
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Read
   is
   begin
      null;
   end Read;

   ------------------------------------------------------------------
   -- CheckWrite
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure CheckWrite (WriteOK : out Boolean)
   is
   begin
      WriteOK := True;
   end CheckWrite;

   ------------------------------------------------------------------
   -- CurrentFloppy
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CurrentFloppy return File.T is (CurrentFile);

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    Creates the Temp Directory if it doesn't exist.
   ------------------------------------------------------------------
   procedure Init
   is
   ---------------------------------------------------------
   -- begin Init
   ---------------------------------------------------------
   begin
      null;
   end Init;

end Floppy;
