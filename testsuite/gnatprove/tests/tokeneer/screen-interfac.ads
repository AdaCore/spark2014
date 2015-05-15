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
-- Screen.Interfac
--
-- Description:
--    An interface for outputs to the Win32 Console.
--
-------------------------------------------------------------------------

private package Screen.Interfac
  with Abstract_State => (Output with External => Async_Readers,
                                      Part_Of  => Screen.Output)
is

   ----------------------------------------------------------------------
   -- Types
   ----------------------------------------------------------------------
   type Colours is (BrightWhite, White, Red, Green, Black);

   type ScreenWidthT  is range 0..80;
   type ScreenHeightT is range 0..30;

   subtype ScreenXCoordT is ScreenWidthT  range 0 .. ScreenWidthT'Last - 1;
   subtype ScreenYCoordT is ScreenHeightT range 0 .. ScreenHeightT'Last - 1;
   type XYCoordT is record
      X : ScreenXCoordT;
      Y : ScreenYCoordT;
   end record;
   ----------------------------------------------------------------------
   -- Operations
   ----------------------------------------------------------------------

   ----------------------------------------------------------------------
   -- Write
   --
   -- Description:
   --    Write to the Win32 Console.
   --
   ---------------------------------------------------------------------
   procedure Write (Buffer : in     String;
                    Colour : in     Colours;
                    Coord  : in     XYCoordT;
                    OK     :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((OK,
                       Output) => (Buffer,
                                   Colour,
                                   Coord));

   ----------------------------------------------------------------------
   -- ClearRegion
   --
   -- Description:
   --    Clears a region of the Console.
   --
   ---------------------------------------------------------------------
   procedure ClearRegion (Left   : in     ScreenXCoordT;
                          Top    : in     ScreenYCoordT;
                          Right  : in     ScreenXCoordT;
                          Bottom : in     ScreenYCoordT;
                          OK     :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((OK,
                       Output) => (Bottom,
                                   Left,
                                   Right,
                                   Top));

   ----------------------------------------------------------------------
   -- Init
   --
   -- Description:
   --    Initialises the Win32 Console.
   --
   ---------------------------------------------------------------------
   procedure Init (OK : out Boolean)
     with Global  => (Output => Output),
          Depends => ((OK,
                       Output) => null);

end Screen.Interfac;
