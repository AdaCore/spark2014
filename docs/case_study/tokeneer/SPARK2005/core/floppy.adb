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
with Win32;
with Win32.WinBase;
with Win32.WinNT;
with Interfaces.C;

use type System.Address;
use type Win32.Bool;
use type Win32.DWord;
use type Win32.Word;
use type Win32.UInt;
use type Interfaces.C.Size_T;

package body Floppy
is


   subtype FilePathNameT is
     Interfaces.C.Char_Array( 0 .. Win32.Winbase.OFS_MAXPATHNAME + 1);

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

   CFloppyDrive : Interfaces.C.Char_Array(0 .. 2);



   ------------------------------------------------------------------
   -- FileAndPathName
   --
   -- Description:
   --    Prepends a path to a file name.
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function FilePathAndName( Path : in String;
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
   function IsPresent return Boolean
   is

      -- Return value.
      Result : Win32.Bool;

      -- Returns from GetVolumeInformation (all unused)
      VolumeName : Interfaces.C.Char_Array( 1 .. 32 );
      SerialNo : aliased Win32.Dword;
      MaxCompLength : aliased Win32.Dword;
      FileSystemFlags : aliased Win32.Dword;
      FileSystemName  : Interfaces.C.Char_Array( 1 .. 256 );

   begin

      Result
        := WIN32.Winbase.GetVolumeInformation
        (CFloppyDrive(CFloppyDrive'First)'Unchecked_Access,
         VolumeName(VolumeName'First)'Unchecked_Access,
         VolumeName'Length,
         SerialNo'Unchecked_Access,
         MaxCompLength'Unchecked_Access,
         FileSystemFlags'Unchecked_Access,
         FileSystemName(FileSystemName'First)'Unchecked_Access,
         FileSystemName'Length );

      return (Result /= Win32.False);

   end IsPresent;

   ------------------------------------------------------------------
   -- Write
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Write(TheFile : in File.T)
   is

      Unused : Boolean;
      FileName : FileNameStringT;
      NameLength : Natural;

      -- Return value.
      Result : Win32.Bool;

      ArchiveName : String := "archive.log";

   begin

      if File.Exists(TheFile => CurrentFile) then

         File.OpenRead (TheFile => CurrentFile,
                    Success => Unused);

         File.Delete ( TheFile => CurrentFile,
                       Success => Unused);

         CurrentFile := File.NullFile;

      end if;

      if File.Exists(TheFile => WrittenFile) then

         File.OpenRead (TheFile => WrittenFile,
                    Success => Unused);

         File.Delete ( TheFile => WrittenFile,
                       Success => Unused);

         WrittenFile := File.NullFile;

      end if;

      File.GetName(TheFile => TheFile,
                   TheName => FileName,
                   NameLength => NameLength);
      -- unlikely to happen but prevent overflow in constructing name.
      if NameLength > FileName'Last then
         NameLength := FileName'Last;
      end if;

      -- Make a copy of the file to be written.
      Result := Win32.Winbase.CopyFile
        (LpExistingFileName =>
           FilePathAndName(Path => ".",
                           Name => FileName( 1 .. NameLength))(0)'Unchecked_Access,
         LpNewFileName =>
           FilePathAndName(Path => TempDir,
                           Name => WrittenName)(0)'Unchecked_Access,
         BFailIfExists => Win32.FALSE);

      WrittenFile := File.Construct(TempDir & "\" & WrittenName);

      -- Write the file to Floppy - must be an audit log file.
      Result := Win32.Winbase.CopyFile
        (LpExistingFileName =>
           FilePathAndName(Path => TempDir,
                           Name => WrittenName)(0)'Unchecked_Access,
         LpNewFileName =>
           FilePathAndName(Path => FloppyDrive,
                           Name => ArchiveName)(0)'Unchecked_Access,
         BFailIfExists => Win32.TRUE);

   end Write;


   ------------------------------------------------------------------
   -- Read
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Read
   is

      FileData : aliased Win32.Winbase.WIN32_FIND_DATA;
      FileHandle : Win32.Winnt.Handle;

      Result : Win32.Bool;

      SearchString : constant Interfaces.C.Char_Array
        := FilePathAndName(FloppyDrive, "*.*");

      Unused : Boolean;

   begin

      if File.Exists(TheFile => CurrentFile) then

         File.OpenRead (TheFile => CurrentFile,
                    Success => Unused);

         File.Delete ( TheFile => CurrentFile,
                       Success => Unused);

         CurrentFile := File.NullFile;

      end if;

      FileHandle := Win32.Winbase.FindFirstFile
        (SearchString(SearchString'First)'Unchecked_Access,
         FileData'Unchecked_Access);

     if FileHandle /= System.Null_Address then

         Result := Win32.Winbase.CopyFile
           (LpExistingFileName =>
              FilePathAndName(Path => FloppyDrive,
                              Name => Interfaces.C.To_Ada
                                       (Interfaces.C.Char_Array(FileData.CFileName),
                                        True))(0)'Unchecked_Access,
            LpNewFileName =>
              FilePathAndName(Path => TempDir,
                              Name => CurrentName)(0)'Unchecked_Access,
            BFailIfExists => Win32.FALSE);

         CurrentFile := File.Construct(TempDir & "\" & CurrentName);
      end if;

   end Read;

   ------------------------------------------------------------------
   -- CheckWrite
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure CheckWrite (WriteOK : out Boolean)
   is
      Unused : Boolean;
   begin
      File.Compare(FileA => CurrentFile,
                   FileB => WrittenFile,
                   FilesTheSame => WriteOK);

      if File.Exists(TheFile => CurrentFile) then

         File.OpenRead (TheFile => CurrentFile,
                    Success => Unused);

         File.Delete ( TheFile => CurrentFile,
                       Success => Unused);

         CurrentFile := File.NullFile;

      end if;

      if File.Exists(TheFile => WrittenFile) then

         File.OpenRead (TheFile => WrittenFile,
                        Success => Unused);

         File.Delete ( TheFile => WrittenFile,
                       Success => Unused);

         WrittenFile := File.NullFile;

      end if;

   end CheckWrite;

   ------------------------------------------------------------------
   -- CurrentFloppy
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   function CurrentFloppy return File.T
   is
   begin
      return CurrentFile;
   end CurrentFloppy;


   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    Creates the Temp Directory if it doesn't exist.
   ------------------------------------------------------------------
   procedure Init
   is
      Success : Boolean;
      Unused : Boolean;

      ------------------------------------------------------------------
      -- SetFloppyDriveLetter
      --
      -- Description:
      --    Obtains the Floppy Drive Letter.
      --    This assumes that the Floppy is the first REMOVABLE drive
      --    found.
      --
      -- Implementation Notes:
      --    None.
      ------------------------------------------------------------------
      procedure SetFloppyDriveLetter
      is

         Drives : Win32.Dword;
         Drive : String(1 .. 3) := "*:\";
         DriveType : Win32.UInt;
         Found : Boolean := False;
      begin
         Drives := Win32.Winbase.GetLogicalDrives;
         for N in 0 .. 31 loop
            if (Drives and 2**N) > 0 then
               Drive(1) := Character'Val(Character'Pos('A') + N);
               DriveType :=
                 Win32.Winbase.GetDriveType
                 (Interfaces.C.To_C(Drive, True)(0)'Unchecked_access);

               -- DRIVE_REMOVEABLE covers both floppy disks and (more likely)
               -- modern USB FLASH drives.
               if DriveType = Win32.Winbase.DRIVE_REMOVABLE then
                  FloppyDrive := Drive(1 .. 2);
                  Found := True;
               end if;
            end if;
            exit when Found;
         end loop;

         CFloppyDrive := Interfaces.C.To_C(FloppyDrive, True);

      end SetFloppyDriveLetter;

   ---------------------------------------------------------
   -- begin Init
   ---------------------------------------------------------
   begin

      -- Tidy up any unwanted temporary files before we start.
      CurrentFile := File.Construct(TempDir & "\" & CurrentName);
      if File.Exists(TheFile => CurrentFile) then

         File.OpenRead (TheFile => CurrentFile,
                        Success => Unused);

         File.Delete ( TheFile => CurrentFile,
                       Success => Unused);
      end if;
      CurrentFile := File.NullFile;

      WrittenFile := File.Construct(TempDir & "\" & WrittenName);
      if File.Exists(TheFile => WrittenFile) then

         File.OpenRead (TheFile => WrittenFile,
                    Success => Unused);

         File.Delete ( TheFile => WrittenFile,
                       Success => Unused);

      end if;
      WrittenFile := File.NullFile;

      SetFloppyDriveLetter;

      File.CreateDirectory(DirName => TempDir,
                           Success => Success );


   end Init;

end Floppy;





