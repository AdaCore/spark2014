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
-- Implementation Notes:
--    This is based on Stream_IO so cannot be Examined by SPARK.
--
------------------------------------------------------------------
with Ada.Streams.Stream_IO;
use type Ada.Streams.Stream_IO.File_Mode;

with Ada.Characters.Latin_1;
with Ada.Characters.Handling;

with Interfaces.C;
use type Interfaces.C.Size_T;

with Text_IO;
with Ada.Exceptions;

package body File
  with SPARK_Mode => Off  --  exception handlers
is

   ------------------------------------------------------------------
   -- IsOpen
   --
   -- Description:
   --    Returns True if the file is open.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function IsOpen (File : T) return Boolean is
     (File.Handle /= null
        and then Ada.Streams.Stream_IO.Is_Open (File.Handle.all));

   ------------------------------------------------------------------
   -- IsIn
   --
   -- Description:
   --    Returns True if the file is open in a readable mode.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function IsIn (File : T) return Boolean is
     (IsOpen (File)
        and then Ada.Streams.Stream_IO.Mode(File.Handle.all) =
                   Ada.Streams.Stream_IO.In_File);

   ------------------------------------------------------------------
   -- IsOut
   --
   -- Description:
   --    Returns True if the file is open in a writable mode.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function IsOut (File : T) return Boolean is
     (IsOpen (File)
        and then (Ada.Streams.Stream_IO.Mode(File.Handle.all) =
                    Ada.Streams.Stream_IO.Out_File or
                    Ada.Streams.Stream_IO.Mode(File.Handle.all) =
                    Ada.Streams.Stream_IO.Append_File));

   ------------------------------------------------------------------
   -- Construct
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function Construct (TheName : CommonTypes.StringF1) return T
   is
     NewName : NameT;
   begin
      if TheName'Last > MaxNameLength then
         NewName.Length := MaxNameLength;
         NewName.Text   := TheName(1..MaxNameLength);
      else
         NewName.Length := TheName'Last;
         NewName.Text(1..TheName'Last) := TheName;
      end if;
      return T'(NewName, null);
   end Construct;

   ------------------------------------------------------------------
   -- SetName
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetName (TheName : in     CommonTypes.StringF1;
                      TheFile : in out T)
   is
   begin
      if TheName'Last > MaxNameLength then
         TheFile.Name.Length := MaxNameLength;
         TheFile.Name.Text   := TheName(1..MaxNameLength);
      else
         TheFile.Name.Length := TheName'Last;
         TheFile.Name.Text(1..TheName'Last) := TheName;
      end if;

   end SetName;

   ------------------------------------------------------------------
   -- GetName
   --
   -- Description:
   --    Gets the name of a file.
   --
   -- Traceunit : C.File.GetName
   -- Traceto   :
   ------------------------------------------------------------------
   procedure GetName (TheFile     : in     T;
                      TheName     :    out String;
                      NameLength  :    out Natural)
   is
   begin
      TheName := (others => ' ');
      if TheName'Length >= TheFile.Name.Length then
         TheName(TheName'First .. TheName'First + TheFile.Name.Length - 1)
           := TheFile.Name.Text(1..TheFile.Name.Length);
      else
         TheName(TheName'First .. TheName'Last)
           := TheFile.Name.Text(1 .. TheName'Length);
      end if;
      NameLength := TheFile.Name.Length;
   end GetName;

   ------------------------------------------------------------------
   -- OpenAppend
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure OpenAppend (TheFile : in out T;
                         Success :    out Boolean)
   is
   begin
      TheFile.Handle := new Ada.Streams.Stream_IO.File_Type;
      Ada.Streams.Stream_IO.Open
        (File => TheFile.Handle.all,
         Mode => Ada.Streams.Stream_IO.Append_File,
         Name => TheFile.Name.Text(1..TheFile.Name.Length),
         Form => "");

      Success := True;
   exception
      when others =>
         Success := False;
   end OpenAppend;

   ------------------------------------------------------------------
   -- OpenWrite
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure OpenWrite (TheFile : in out T;
                        Success :    out Boolean)
   is
   begin
      TheFile.Handle := new Ada.Streams.Stream_IO.File_Type;
      Ada.Streams.Stream_IO.Open
        (File => TheFile.Handle.all,
         Mode => Ada.Streams.Stream_IO.Out_File,
         Name => TheFile.Name.Text(1..TheFile.Name.Length),
         Form => "");

      Success := True;
   exception
      when others =>
         Success := False;
   end OpenWrite;

   ------------------------------------------------------------------
   -- OpenRead
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure OpenRead ( TheFile : in out T ;
                        Success :    out Boolean )
   is
   begin
      TheFile.Handle := new Ada.Streams.Stream_IO.File_Type;
      Ada.Streams.Stream_IO.Open
        (File => TheFile.Handle.all,
         Mode => Ada.Streams.Stream_IO.In_File,
         Name => TheFile.Name.Text(1..TheFile.Name.Length),
         Form => "");

      Success := True;
   exception
      when others =>
         Success := False;
   end OpenRead;

   ------------------------------------------------------------------
   -- PutChar
   --
   -- Description:
   --    Writes a character to file.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure PutChar (TheFile : in out T;
                      Item    : in     Character)
   is
      Strm : Ada.Streams.Stream_IO.Stream_Access;
   begin

      if IsOut(TheFile) then
         Strm := Ada.Streams.Stream_IO.Stream(TheFile.Handle.all);

         Character'Write(Strm, Item);
      end if;

   exception
      when others => null;
   end PutChar;

   ------------------------------------------------------------------
   -- Close
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Close (TheFile : in out T;
                    Success :    out Boolean)
   is
   begin

      Ada.Streams.Stream_IO.Close
        (File => TheFile.Handle.all);
      Success := True;
   exception
      when others =>
         Success := False;
   end Close;

   ------------------------------------------------------------------
   -- Exists
   --
   -- Implementation Notes:
   --    A file exists if it is open or can be opened.
   --
   ------------------------------------------------------------------
   function Exists (TheFile : T) return Boolean
   is
      CloseOK : Boolean;
      Result  : Boolean;
      TempF   : T := TheFile;
   begin

      if IsOpen(TheFile) then
         Result := True;
      else

         OpenRead (TheFile => TempF,
                   Success => Result);
         if Result then
            Close (TheFile => TempF,
                   Success => CloseOK);
         end if;
      end if;

      return Result;

   end Exists;

   ------------------------------------------------------------------
   -- PutString
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure PutString (TheFile : in out T;
                        Text    : in     String;
                        Stop    : in     Natural)
   is
      Strm     : Ada.Streams.Stream_IO.Stream_Access;
      FinalStr : Positive;
      Final    : Positive;
   begin

      if IsOut(TheFile) then
         if Stop = 0 then
            Final := Text'Last;
            FinalStr := Text'Last;
         else
            Final := Stop + Text'First - 1;
            if Stop <= Text'Length then
               FinalStr := Stop + Text'First - 1;
            else
               FinalStr := Text'Last;
            end if;
         end if;
         Strm := Ada.Streams.Stream_IO.Stream(TheFile.Handle.all);

         for I in Positive range Text'First .. FinalStr loop
            Character'Write(Strm, Text(I));
         end loop;
         for I in Positive range FinalStr + 1 .. Final loop
            Character'Write(Strm, ' ');
         end loop;
      end if;

   exception
      when others => null;
   end PutString;

   ------------------------------------------------------------------
   -- GetString
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetString (TheFile : in out T;
                        Text    :    out String;
                        Stop    :    out Natural)
   is
      Strm : Ada.Streams.Stream_IO.Stream_Access;
   begin
      Stop := Text'First - 1;
      if IsIn (TheFile) then
         Strm := Ada.Streams.Stream_IO.Stream(TheFile.Handle.all);
         loop
            exit when EndOfFile(TheFile);
            Stop := Stop + 1;
            Character'Read(Strm, Text(Stop));
            exit when Stop = Text'Last;
         end loop;
      end if;
   exception
      when others => null;
   end GetString;

   ------------------------------------------------------------------
   -- GetChar
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetChar (TheFile : in out T;
                      Item    :    out Character)
   is
      Strm : Ada.Streams.Stream_IO.Stream_Access;
   begin
      if IsIn (TheFile) then
         Strm := Ada.Streams.Stream_IO.Stream(TheFile.Handle.all);
         Character'Read(Strm, Item);
      else
         Item := Character'First;
      end if;

   exception
      when others =>
         Item := Character'First;
   end GetChar;

   ------------------------------------------------------------------
   -- PutInteger
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure PutInteger (TheFile : in out T;
                         Item    : in Integer;
                         Width   : in Natural)
   is
      Str : String := Integer'Image(Item);
      PaddingCount : Integer := Width - Str'Length;
      Start : Positive := Str'First;
   begin
      if Item >= 0 then
         PaddingCount := PaddingCount + 1;
         Start := Start + 1;
      end if;
      while PaddingCount > 0 loop
         PutChar ( TheFile, ' ');
         PaddingCount := PaddingCount -1;
      end loop;
      PutString (TheFile, Str( Start .. Str'Last), 0);
   end PutInteger;

   ------------------------------------------------------------------
   -- GetInteger
   --
   -- Implementation Notes:
   --    If the Width is 0 then skip new lines, spaces until we reach
   --    the number.
   --    If the Width is not 0 then only character preceeding integer
   --    is ' ' (No new lines).
   ------------------------------------------------------------------
   procedure GetInteger (TheFile : in out T;
                         Item    :    out Integer;
                         Width   : in     Natural;
                         Success :    out Boolean)
   is
      Ch           : Character;
      FileIndex    : Ada.Streams.Stream_IO.Positive_Count;
      Count        : Natural := Width;
      LastStrIndex : Positive := Integer'Image(Integer'First)'Last;
      StrIndex     : Positive := 1;
      IntStr       : String (1 .. LastStrIndex) := (others => ' ');
   begin
      Success := True;
      Item    := 0;
      if Width = 0 then
         loop
            if EndOfFile(TheFile) then
               Success := False;
               exit;
            end if;
            if EndOfLine(TheFile) then
               SkipLine(TheFile, 1);
               Ch := ' ';
            else
               GetChar(TheFile, Ch);
            end if;
            if Ch = '+' then
               IntStr(StrIndex) := Ch;
               exit;
            end if;
            if Ch = '-' then
               IntStr(StrIndex) := Ch;
               exit;
            end if;
            if Ada.Characters.Handling.Is_Digit(Ch) then
               StrIndex := StrIndex + 1;
               IntStr(StrIndex) := Ch;
               exit;
            end if;
            if Ch /= ' ' then
               Success := False;
               exit;
            end if;
         end loop;

         if Success then
            --Start building number
            while not EndOfFile(TheFile) loop
               FileIndex := Ada.Streams.Stream_IO.Index(TheFile.Handle.all);
               GetChar(TheFile, Ch);
               if not Ada.Characters.Handling.Is_Digit(Ch) then
                  Ada.Streams.Stream_IO.Set_Index(TheFile.Handle.all,
                                                  FileIndex);
                  exit;
               end if;
               StrIndex := StrIndex + 1;
               IntStr(StrIndex) := Ch;
            end loop;

         end if;

      else
         -- only get Width Characters
         while Count > 0 loop
            exit when EndOfLine(TheFile);
            Count := Count - 1;
            GetChar(TheFile, Ch);
            if Ch = '+' then
               exit;
            end if;
            if Ch = '-' then
               IntStr(StrIndex) := Ch;
               exit;
            end if;
            if Ada.Characters.Handling.Is_Digit(Ch) then
               StrIndex := StrIndex + 1;
               IntStr(StrIndex) := Ch;
               exit;
            end if;
            if Ch /= ' ' then
               Success := False;
               exit;
            end if;
         end loop;

         while Count > 0 loop
            exit when EndOfLine(TheFile);
            Count := Count - 1;
            GetChar(TheFile, Ch);
            if not Ada.Characters.Handling.Is_Digit(Ch) then
               Success := False;
            else
               StrIndex := StrIndex + 1;
               IntStr(StrIndex) := Ch;
            end if;
         end loop;

      end if;

      Item := Integer'Value(IntStr);

   exception
      when others =>
         Success := False;
   end GetInteger;

   ------------------------------------------------------------------
   -- NewLine
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure NewLine (TheFile : in out T;
                      Spacing : in     Natural)
   is
   begin
      if IsOut (TheFile) then
         for I in Natural range 1 .. Spacing loop
            PutChar(TheFile, Ada.Characters.Latin_1.CR);
            PutChar(TheFile, Ada.Characters.Latin_1.LF);
         end loop;
      end if;
   end NewLine;

   ------------------------------------------------------------------
   -- SkipLine
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SkipLine (TheFile  : in out T;
                       Spacing  : in     Positive)
   is
      procedure SkipOneLine
      is
         DiscardedChar : Character;
      begin
         while not EndOfFile(TheFile) loop
            GetChar (TheFile, DiscardedChar);
            exit when DiscardedChar = Ada.Characters.Latin_1.LF;
         end loop;
      end SkipOneLine;

   begin
      if IsIn (TheFile) then

         for I in Positive range 1 .. Spacing loop
            SkipOneLine;
         end loop;

      end if;

   end SkipLine;

   ------------------------------------------------------------------
   -- GetLine
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetLine (TheFile  : in out T;
                      Item     :    out String;
                      Stop     :    out Natural)
   is
      Strm : Ada.Streams.Stream_IO.Stream_Access;
   begin
      Stop := Item'First - 1;
      if IsIn (TheFile) then
         Strm := Ada.Streams.Stream_IO.Stream(TheFile.Handle.all);
         loop
            if EndOfLine(TheFile) then
               SkipLine(TheFile, 1);
               exit;
            end if;
            exit when Stop = Item'Last;
            Stop := Stop + 1;
            Character'Read(Strm, Item(Stop));
         end loop;
      end if;
   exception
      when others => null;
   end GetLine;

   ------------------------------------------------------------------
   -- EndOfFile
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function EndOfFile (TheFile : T) return Boolean
   is
      EOF : Boolean;
   begin
      if IsIn (TheFile) then
         EOF := Ada.Streams.Stream_IO.End_Of_File(TheFile.Handle.all);
      else
         EOF := True;
      end if;
      return EOF;
   end EndOfFile;

   ------------------------------------------------------------------
   -- EndOfLine
   --
   -- Implementation Notes:
   --    EOL is either CF.LF or just LF.
   --
   ------------------------------------------------------------------
   function EndOfLine (TheFile : T) return Boolean
   is
      EOLChar : Character;
      FileIndex : Ada.Streams.Stream_IO.Positive_Count;
      Result : Boolean;
      TempF : T := TheFile;
   begin
      FileIndex := Ada.Streams.Stream_IO.Index(TempF.Handle.all);

      if EndOfFile(TempF) then
         Result := True;
      else
         GetChar(TheFile => TempF, Item => EOLChar);
         if EOLChar = Ada.Characters.Latin_1.CR then
            -- is next character a LF?
            GetChar(TheFile => TempF, Item => EOLChar);
         end if;
         if EOLChar = Ada.Characters.Latin_1.LF then
            Result := True;
         else
            Result := False;
         end if;

         Ada.Streams.Stream_IO.Set_Index(File => TempF.Handle.all,
                                         To   => FileIndex);

      end if;

      return Result;
   end EndOfLine;
   ------------------------------------------------------------------
   -- Create
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Create (TheFile : in out T;
                     Success :    out Boolean)
   is
   begin

      TheFile.Handle := new Ada.Streams.Stream_IO.File_Type;
      Ada.Streams.Stream_IO.Create
        ( File => TheFile.Handle.all,
          Mode => Ada.Streams.Stream_IO.Out_File,
          Name => TheFile.Name.Text(1..TheFile.Name.Length),
          Form => "" );

      Success := True;
   exception
      when others =>
            Success := False;
   end Create;

   ------------------------------------------------------------------
   -- Delete
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Delete ( TheFile : in out T;
                      Success :    out Boolean)
   is
   begin
      Ada.Streams.Stream_IO.Delete ( File   => TheFile.Handle.all);
      Success := True;
   exception
      when others =>
            Success := False;
   end Delete;

   ------------------------------------------------------------------
   -- Compare
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Compare (FileA        : in out T;
                      FileB        : in out T;
                      FilesTheSame :    out Boolean)
   is
      Success      : Boolean;
      CharA, CharB : Character;
   begin
      if FileA.Name = FileB.Name then
         Success := True;
      else

         OpenRead(TheFile => FileA,
                  Success => Success);
         if Success then

            OpenRead(TheFile => FileB,
                     Success => Success);

            if Success then

               loop
                  if EndOfFile(FileA) and EndOfFile(FileB) then
                     exit;
                  end if;
                  if (EndOfFile(FileA) and not EndOfFile(FileB))
                    or else (not EndOfFile(FileA) and EndOfFile(FileB))
                  then
                     Success := False;
                     exit;
                  end if;

                  GetChar(TheFile => FileA, Item => CharA);
                  GetChar(TheFile => FileB, Item => CharB);

                  if CharA /= CharB then
                     Success := False;
                     exit;
                  end if;

               end loop;
            end if;
         end if;
      end if;

      FilesTheSame := Success;

      Close(TheFile => FileA,
            Success => Success);

      Close(TheFile => FileB,
            Success => Success);
   end Compare;

   ------------------------------------------------------------------
   -- Copy
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure Copy (FileA        : in out T;
                   FileB        : in out T;
                   Success      :    out Boolean)

   is
      CharA : Character;
   begin

      OpenRead(TheFile => FileA,
               Success => Success);
      if Success then

         OpenAppend(TheFile => FileB,
                    Success => Success);

         if not Success then
            Create(TheFile => FileB,
                   Success => Success);
         end if;

         if Success then

            while not EndOfFile(FileA) loop

               GetChar(TheFile => FileA, Item => CharA);
               PutChar(TheFile => FileB, Item => CharA);

            end loop;
         end if;
      end if;

      Close(TheFile => FileA,
            Success => Success);

      Close(TheFile => FileB,
            Success => Success);
   end Copy;

   ------------------------------------------------------------------
   -- CreateDirectory
   --
   -- Implementation Notes:
   --    None.
   ------------------------------------------------------------------
   procedure CreateDirectory (DirName : in String;
                              Success : out Boolean)
   is
    begin
       Success := True;
   end CreateDirectory;

end File;
