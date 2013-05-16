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
-- File
--
-- Description:
--    Provides file utilities.
--
------------------------------------------------------------------
with Ada.Streams.Stream_IO; -- only used in hidden private part

package File
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   type T is private;

   MaxNameLength : constant := 255;

   NullFile : constant T;

   ------------------------------------------------------------------
   -- SetName
   --
   -- Description:
   --    Sets the name of a file.
   --
   -- Traceunit : C.File.SetName
   ------------------------------------------------------------------
   procedure SetName (TheName : in     String;
                      TheFile : in out T);
   --# derives
   --#   TheFile from
   --#      TheName,
   --#      TheFile;

   ------------------------------------------------------------------
   -- GetName
   --
   -- Description:
   --    Gets the name of a file.
   --
   -- Traceunit : C.File.GetName
   ------------------------------------------------------------------
   procedure GetName (TheFile     : in     T;
                      TheName     :    out String;
                      NameLength  :    out Natural);
   --# derives TheName,
   --#         NameLength from TheFile;
   ------------------------------------------------------------------
   -- Construct
   --
   -- Description:
   --    Creates the initial file entity.
   --
   -- Traceunit : C.File.Construct
   ------------------------------------------------------------------
   function Construct (TheName : String) return T;
   --# pre TheName'Last <= MaxNameLength;

   ------------------------------------------------------------------
   -- OpenAppend
   --
   -- Description:
   --    Opens the file for appending.
   --
   -- Traceunit : C.File.OpenAppend
   ------------------------------------------------------------------
   procedure OpenAppend ( TheFile : in out T ;
                          Success :    out Boolean );
   --# derives
   --#   Success,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- OpenWrite
   --
   -- Description:
   --    Opens the file for writing.
   --
   -- Traceunit : C.File.OpenWrite
   ------------------------------------------------------------------
   procedure OpenWrite ( TheFile : in out T ;
                         Success :    out Boolean );
   --# derives
   --#   Success,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- OpenRead
   --
   -- Description:
   --    Opens the file for reading.
   --
   -- Traceunit : C.File.OpenRead
   ------------------------------------------------------------------
   procedure OpenRead ( TheFile : in out T ;
                        Success :    out Boolean );
   --# derives
   --#   Success,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- Close
   --
   -- Description:
   --    Closes the file.
   --
   -- Traceunit : C.File.Close
   ------------------------------------------------------------------
   procedure Close ( TheFile : in out T ;
                     Success :    out Boolean );
   --# derives
   --#   Success,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- Exists
   --
   -- Description:
   --    Returns True if the file exists.
   --
   -- Traceunit : C.File.Exists
   ------------------------------------------------------------------
   function Exists ( TheFile : T ) return Boolean;

   ------------------------------------------------------------------
   -- PutString
   --
   -- Description:
   --    Writes the string to file.
   --    If Stop = 0 or Stop >= Text'Length then writes all of Text
   --    If Stop < Text'Length writes first Stop characters from string.
   --
   -- Traceunit : C.File.PutString
   ------------------------------------------------------------------
   procedure PutString ( TheFile : in out T;
                         Text    : in     String;
                         Stop    : in     Natural);
   --# derives
   --#   TheFile from
   --#      TheFile,
   --#      Text,
   --#      Stop;

   ------------------------------------------------------------------
   -- GetString
   --
   -- Description:
   --    Reads the string from file.
   --    Stop gives the number of characters actually read.
   --
   -- Traceunit : C.File.GetString
   ------------------------------------------------------------------
   procedure GetString ( TheFile : in out T;
                         Text    :    out String;
                         Stop    :    out Natural);
   --# derives
   --#   Text,
   --#   Stop,
   --#   TheFile from
   --#      TheFile;


   ------------------------------------------------------------------
   -- GetChar
   --
   -- Description:
   --    Reads a character from file.
   --
   -- Traceunit : C.File.GetChar
   ------------------------------------------------------------------
   procedure GetChar ( TheFile : in out T;
                       Item    :    out Character);
   --# derives
   --#   Item,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- PutInteger
   --
   -- Description:
   --    Writes the integer to file.
   --
   -- Traceunit : C.File.PutInteger
   ------------------------------------------------------------------
   procedure PutInteger ( TheFile : in out T;
                          Item    : in Integer;
                          Width   : in Natural);
   --# derives
   --#   TheFile from
   --#      TheFile,
   --#      Item,
   --#      Width;

   ------------------------------------------------------------------
   -- GetInteger
   --
   -- Description:
   --    Gets an Integer from file.
   --
   -- Traceunit : C.File.GetInteger
   ------------------------------------------------------------------
   procedure GetInteger ( TheFile : in out T;
                          Item    :    out Integer;
                          Width   : in     Natural;
                          Success :    out Boolean);
   --# derives
   --#   Item,
   --#   Success,
   --#   TheFile from
   --#      TheFile,
   --#      Width;
   ------------------------------------------------------------------
   -- NewLine
   --
   -- Description:
   --    Writes spacing number of new lines (CR LF) to file.
   --
   -- Traceunit : C.File.NewLine
   ------------------------------------------------------------------
   procedure NewLine ( TheFile : in out T;
                       Spacing : in     Natural);
   --# derives
   --#   TheFile from *,
   --#      Spacing;

   ------------------------------------------------------------------
   -- SkipLine
   --
   -- Description:
   --    Skips spacing lines in a file open for reading
   --    any problems and it does nothing.
   --
   -- Traceunit : C.File.SkipLine
   ------------------------------------------------------------------
   procedure SkipLine ( TheFile  : in out T;
                        Spacing  : in     Positive);
   --# derives
   --#   TheFile from *,
   --#      Spacing;

   ------------------------------------------------------------------
   -- GetLine
   --
   -- Description:
   --    Gets a string upto the next new line or max length of string
   --    which ever is sooner.
   --    Stop gives the number of characters read.
   --
   -- Traceunit : C.File.GetLine
   ------------------------------------------------------------------
   procedure GetLine ( TheFile  : in out T;
                       Item     :    out String;
                       Stop     :    out Natural);
   --# derives
   --#      Item,
   --#      Stop,
   --#   TheFile from TheFile;

   ------------------------------------------------------------------
   -- EndOfFile
   --
   -- Description:
   --    Returns true when the next element in the file is EOF.
   --
   -- Traceunit : C.File.EndOfFile
   ------------------------------------------------------------------
   function EndOfFile ( TheFile : T ) return Boolean;

   ------------------------------------------------------------------
   -- EndOfLine
   --
   -- Description:
   --    Returns true when the next element in the file is LF CR.
   --
   -- Traceunit : C.File.EndOfLine
   ------------------------------------------------------------------
   function EndOfLine ( TheFile : T ) return Boolean;

   ------------------------------------------------------------------
   -- Create
   --
   -- Description:
   --    Creates the file.
   --
   -- Traceunit : C.File.Create
   ------------------------------------------------------------------
   procedure Create ( TheFile : in out T;
                      Success :    out Boolean);
   --# derives
   --#   Success,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- Delete
   --
   -- Description:
   --    Deletes the file.
   --
   -- Traceunit : C.File.Delete
   ------------------------------------------------------------------
   procedure Delete ( TheFile : in out T;
                      Success :    out Boolean);
   --# derives
   --#   Success,
   --#   TheFile from
   --#      TheFile;

   ------------------------------------------------------------------
   -- Compare
   --
   -- Description:
   --    Compares FileA with FileB.
   --
   -- Traceunit : C.File.Copy
   ------------------------------------------------------------------
   procedure Compare ( FileA        : in out T;
                       FileB        : in out T;
                       FilesTheSame :    out Boolean );
   --# derives
   --#   FilesTheSame from
   --#      FileA,
   --#      FileB &
   --#   FileA,
   --#   FileB from * ;

   ------------------------------------------------------------------
   -- Copy
   --
   -- Description:
   --    Copies FileA to FileB, if FileB exists then the contents of
   --    FileA are appended to FileB.
   --
   -- Traceunit : C.File.Copy
   ------------------------------------------------------------------
   procedure Copy ( FileA        : in out T;
                    FileB        : in out T;
                    Success      :    out Boolean );
   --# derives
   --#   Success,
   --#   FileB from
   --#      FileA,
   --#      FileB &
   --#   FileA from * ;

   ------------------------------------------------------------------
   -- CreateDirectory
   --
   -- Description:
   --    Creates the named directory if it does not exist.
   --
   -- Traceunit : C.File.CreateDirectory
   ------------------------------------------------------------------
   procedure CreateDirectory ( DirName : in String;
                               Success : out Boolean);
   --# derives
   --#   Success from
   --#      DirName;

private

   --# hide File;
   -- hidden due to use of access types, required in low level file
   -- handling.

   subtype NameLengthT is Natural range 0 .. MaxNameLength;
   subtype NameI is Positive range 1 .. MaxNameLength;
   subtype NameTextT is String(NameI);

   type NameT is record
      Text   : NameTextT;
      Length : NameLengthT;
   end record;

   type FilePtr is access Ada.Streams.Stream_IO.File_Type;

   type T is record
      Name : NameT;
      Handle : FilePtr := null;
   end record;

   NullFile : constant T := T'(NameT'( NameTextT'(others => ' '),
                                       0),
                               null);

end File;
