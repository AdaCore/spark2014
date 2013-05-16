------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

-------------------------------------------------------------------------
-- Screen.Interface
--
-- Implementation Notes:
--    Not Examined.
--
-------------------------------------------------------------------------
with Ada.Characters.Latin_1;
with Interfaces.C;

with Win32.WinCon;
with Win32.WinBase;
with Win32.Winnt;

use type Win32.Bool;
use type Win32.DWord;
use type Win32.Word;
use type Interfaces.C.Short;

package body Screen.Interface
is

   ----------------------------------------------------------------------
   -- Types
   ----------------------------------------------------------------------
   BrightRedOnBlack : constant Win32.Word
     := Win32.WinCon.FOREGROUND_RED or
        Win32.WinCon.FOREGROUND_INTENSITY;

   BrightGreenOnBlack : constant Win32.Word
     := Win32.WinCon.FOREGROUND_GREEN or
        Win32.WinCon.FOREGROUND_INTENSITY;

   BrightWhiteOnBlack : constant Win32.Word
     := Win32.WinCon.FOREGROUND_BLUE or
        Win32.WinCon.FOREGROUND_GREEN or
        Win32.WinCon.FOREGROUND_RED or
        Win32.WinCon.FOREGROUND_INTENSITY;

   WhiteOnBlack : constant Win32.Word
     := Win32.WinCon.FOREGROUND_BLUE or
        Win32.WinCon.FOREGROUND_GREEN or
        Win32.WinCon.FOREGROUND_RED;

   type Colour_Table_Array is array (Colours) of Win32.Word;
   Colour_Table : constant Colour_Table_Array :=
     (White => WhiteOnBlack,
      BrightWhite => BrightWhiteOnBlack,
      Red   => BrightRedOnBlack,
      Green => BrightGreenOnBlack,
      Black => 0);               -- black background is free


   ----------------------------------------------------------------------
   -- Operations
   ----------------------------------------------------------------------

   ----------------------------------------------------------------------
   -- FillRegion
   --
   -- Description:
   --    Fills the specified region with the given character and
   --    Attributes.
   --
   -- Implementation Notes:
   --    None.
   --
   ---------------------------------------------------------------------
   procedure FillRegion
     (Left    : in     ScreenXCoordT;
      Top     : in     ScreenYCoordT;
      Right   : in     ScreenXCoordT;
      Bottom  : in     ScreenYCoordT;
      Attrib  : in     Win32.Word;
      Char    : in     Character;
      OK      :    out Boolean)
   is
      -- Handle to Console.
      OutCon : Win32.WinNT.Handle
        := Win32.WinBase.GetStdHandle(Win32.WinBase.Std_Output_Handle);

      Width  : ScreenWidthT := (Right + 1 - Left);
      Height : ScreenHeightT := (Bottom + 1 - Top);
      DataSize : Integer := Integer(Width) * Integer(Height);

      subtype DataI is Positive range  1 .. DataSize;
      type DataT is array ( DataI ) of aliased Win32.WinCon.CHAR_INFO;

      Data : aliased DataT;

      -- Return value.
      Result : Win32.Bool;

      DataStartCoord : aliased Win32.WinCon.Coord := (0, 0);

      DataCopyRegion : Win32.WinCon.Coord := (Win32.Short(Width),
                                              Win32.Short(Height));

      WindowRect : aliased Win32.WinCon.Small_Rect
        := (Win32.Short(Left),
            Win32.Short(Top),
            Win32.Short(Right),
            Win32.Short(Bottom));

   begin

      Data := DataT'(others => (Attributes => Attrib,
                                Char => (Win32.WinCon.AsciiChar_Kind,
                                         Win32.CHAR'(Interfaces.C.To_C(Char)))));

      Result := Win32.WinCon.WriteConsoleOutput
        (OutCon,
         Data(Data'First)'Unchecked_Access,
         DataCopyRegion,
         DataStartCoord,
         WindowRect'Unchecked_Access);

      OK := Result /= Win32.False;

   end FillRegion;

   ----------------------------------------------------------------------
   -- Write
   --
   -- Implementation Notes:
   --    None.
   --
   ---------------------------------------------------------------------
   procedure Write(Buffer   : in     String;
                   Colour   : in     Colours;
                   Coord    : in     XYCoordT;
                   OK       :    out Boolean)
   is
      -- Handle to Console.
      Con : Win32.WinNT.Handle
        := Win32.WinBase.GetStdHandle(Win32.WinBase.Std_Output_Handle);

      -- Storage for function out parameter.
      Written      : aliased Win32.Dword;

      Data : Interfaces.C.Char_Array := Interfaces.C.To_C(Buffer, False);

      -- Return value.
      Result : Win32.Bool;

   begin

      Result := Win32.WinCon.FillConsoleOutputAttribute(
                             Con,
                             Colour_Table(Colour),
                             Win32.DWord(Buffer'Length),
                             (Win32.Short(Coord.X), Win32.Short(Coord.Y)),
                             Written'Unchecked_Access);

      OK := (Result /= Win32.False)      and
            (Written = Win32.DWord(Buffer'Length));

      Result := Win32.WinCon.WriteConsoleOutputCharacter(
                             Con,
                             Data(Data'First)'Unchecked_Access,
                             Win32.DWord(Buffer'Length),
                             (Win32.Short(Coord.X), Win32.Short(Coord.Y)),
                             Written'Unchecked_Access);


      OK := OK and (Result /= Win32.False)      and
            (Written = Win32.DWord(Buffer'Length));

   end Write;

   ----------------------------------------------------------------------
   -- ClearRegion
   --
   -- Implementation Notes:
   --    None.
   --
   ---------------------------------------------------------------------
   procedure ClearRegion
     (Left    : in     ScreenXCoordT;
      Top     : in     ScreenYCoordT;
      Right   : in     ScreenXCoordT;
      Bottom  : in     ScreenYCoordT;
      OK      :    out Boolean)
   is
   begin
      FillRegion(Left   => Left,
                 Top    => Top,
                 Right  => Right,
                 Bottom => Bottom,
                 Attrib => WhiteOnBlack,
                 Char   => ' ',
                 OK     => OK);
   end ClearRegion;

   ----------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   ---------------------------------------------------------------------
   procedure Init(OK : out Boolean)
   is

      -- Handle to Console.
      OutCon : Win32.WinNT.Handle
        := Win32.WinBase.GetStdHandle(Win32.WinBase.Std_Output_Handle);
      InCon  : Win32.WinNT.Handle
        := Win32.WinBase.GetStdHandle(Win32.WinBase.Std_Input_Handle);

      Text : aliased Win32.CHAR_Array
        := "Tokeneer ID Station (v1.0) - Administrator's Console ";

      -- Return value.
      Result     : Win32.Bool;

      BufferInfo : aliased Win32.WinCon.Console_Screen_Buffer_Info;
      BufferSize : Win32.WinCon.Coord;

      WindowRect : aliased Win32.WinCon.Small_Rect;

      DrawOK : Boolean;

      ----------------------------------------------------------------------
      -- DrawTemplate
      --
      -- Description:
      --   Completes the Framework for the Screen.
      --
      -- Implementation Notes:
      --    None.
      --
      ---------------------------------------------------------------------
      procedure DrawTemplate( Success : out Boolean)
      is
         ConsoleOK : Boolean;

      begin

         FillRegion( 0,  2, 79,  2, WhiteOnBlack, '-', ConsoleOK);
         Success := ConsoleOK;

         FillRegion( 0,  5, 79,  5, WhiteOnBlack, '-', ConsoleOK);
         Success := Success and ConsoleOK;

         FillRegion( 0, 20, 79, 20, WhiteOnBlack, '-', ConsoleOK);
         Success := Success and ConsoleOK;

         FillRegion(30, 21, 30, 29, WhiteOnBlack, '|', ConsoleOK);
         Success := Success and ConsoleOK;

         Write("CONFIGURATION DATA", BrightWhite, (28, 6), ConsoleOK);
         Success := Success and ConsoleOK;

         Write("ALARMS", BrightWhite, (10, 21), ConsoleOK);
         Success := Success and ConsoleOK;

         Write("Door", White, (2, 24), ConsoleOK);
         Success := Success and ConsoleOK;

         Write("Audit Log", White, (2, 26), ConsoleOK);
         Success := Success and ConsoleOK;

         Write("STATISTICS", BrightWhite, (45, 21), ConsoleOK);
         Success := Success and ConsoleOK;

         Write(">>", BrightWhite, (0, 4), ConsoleOK);
         Success := Success and ConsoleOK;

      end DrawTemplate;

   -------------------------------------------------------------
   -- begin Init
   -------------------------------------------------------------

   begin

      Result := Win32.WinCon.FreeConsole;
      OK := (Result /= Win32.False);

      if OK then

         Result := Win32.WinCon.AllocConsole;
         OK := (Result /= Win32.False);

         if OK then

            WindowRect := (Left   => 0,
                           Top    => 0,
                           Right  => Win32.Short(ScreenXCoordT'Last),
                           Bottom => Win32.Short(ScreenYCoordT'Last));

            -- this gives the current window size.
            Result :=
              Win32.WinCon.GetConsoleScreenBufferInfo
              (OutCon,
               BufferInfo'Unchecked_Access);

            OK := (Result /= Win32.False);

            -- if the window is too narrow or too short
            -- enlarge the buffer in the necessary dimension to
            -- allow the window to be resized.
            -- Otherwise re-size the buffer to the screen size.

            BufferSize.X := BufferInfo.SrWindow.Right -
              BufferInfo.SrWindow.Left + 1;
            BufferSize.Y := BufferInfo.SrWindow.Bottom -
              BufferInfo.SrWindow.Top + 1;

            if BufferSize.X < Win32.Short(ScreenWidthT'Last) then
               BufferSize.X := Win32.Short(ScreenWidthT'Last);
            end if;

            if BufferSize.Y < Win32.Short(ScreenHeightT'Last) then
               BufferSize.Y := Win32.Short(ScreenHeightT'Last);
            end if;

            Result := Win32.WinCon.SetConsoleScreenBufferSize
              (OutCon, BufferSize);

            OK := OK and (Result /= Win32.False);
            -- buffer is now at least as big as the required window
            -- (in both dimensions)

            -- set the window size.
            Result := Win32.WinCon.SetConsoleWindowInfo
                (OutCon, Win32.TRUE, WindowRect'Unchecked_Access);

            OK := OK and (Result /= Win32.False);

            -- shrink the buffer if necessary.
            Result := Win32.WinCon.SetConsoleScreenBufferSize
              (OutCon,
               (Win32.Short(ScreenWidthT'Last), Win32.Short(ScreenHeightT'Last)));

            OK := OK and (Result /= Win32.False);

            Result := Win32.WinCon.SetConsoleTitle
              (Text(Text'First)'Unchecked_Access);

            OK := OK and (Result /= Win32.False);

            Result := Win32.WinCon.SetConsoleTextAttribute
              (OutCon, Colour_Table(White));

            DrawTemplate(DrawOK);

            OK := OK and DrawOK;

         end if;

      end if;

   end Init;

end Screen.Interface;

