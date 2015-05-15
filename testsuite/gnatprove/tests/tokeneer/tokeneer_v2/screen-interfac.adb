package body Screen.Interfac
  with SPARK_Mode => Off
is
   -----------
   -- Write --
   -----------
   procedure Write (Buffer : in     String;
                    Colour : in     Colours;
                    Coord  : in     XYCoordT;
                    OK     :    out Boolean)
   is
   begin
      --  Generated stub: replace with real body!
      OK := True;
   end Write;

   -----------------
   -- ClearRegion --
   -----------------
   procedure ClearRegion (Left   : in     ScreenXCoordT;
                          Top    : in     ScreenYCoordT;
                          Right  : in     ScreenXCoordT;
                          Bottom : in     ScreenYCoordT;
                          OK     :    out Boolean)
   is
   begin
      --  Generated stub: replace with real body!
      OK := True;
   end ClearRegion;

   ----------
   -- Init --
   ----------
   procedure Init (OK : out Boolean) is
   begin
      --  Generated stub: replace with real body!
      OK := True;
   end Init;

end Screen.Interfac;
