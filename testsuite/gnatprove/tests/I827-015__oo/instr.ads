package Instr is

   --   Instruments for a Dashboard
   --
   --   Instrument ---- Speedometer
   --              |
   --              ---- Gauge ---- Graphic_Gauge
   --              |
   --              ---- Clock ---- Chronometer

   -----------------
   --  Root Type  --
   -----------------

   type Instrument is abstract tagged private;

   procedure Set_Name (X : in out Instrument; S : String) with
     Global => null;
   procedure Display_Value (X : Instrument) with
     Global => null;

   -------------------
   --  Speedometer  --
   -------------------

   subtype Speed is Integer range 0 .. 85; -- mph

   type Speedometer is new Instrument with private;
   procedure Display_Value (X : Speedometer) with
     Global => null;

   procedure Set   (X : in out Speedometer'Class; V : Speed) with
     Global => null;
   function  Value (X : Speedometer'Class) return Speed with
     Global => null;

   -----------------
   --   Gauges    --
   -----------------

   subtype Percent is Integer range 0 .. 100;

   type Gauge is new Instrument with private;

   procedure Display_Value (X : Gauge) with
     Global => null;
   procedure Set   (X : in out Gauge'Class; V : Percent) with
     Global => null;
   function  Value (X : Gauge'Class) return Percent with
     Global => null;

   type Graphic_Gauge is new Gauge with private;

   procedure Display_Value (X : Graphic_Gauge) with
     Global => null;

   -----------------
   --   Clocks    --
   -----------------

   subtype Sixty is Integer range 0 .. 60;
   subtype Twenty_Four is Integer range 0 .. 24;

   type Clock is new Instrument with private;
   procedure Display_Value (X : Clock) with
     Global => null;

   procedure Init (X : in out Clock'Class;
                   H : Twenty_Four := 0;
                   M, S : Sixty := 0) with
     Global => null;
   function Seconds (X : Clock'Class) return Sixty with
     Global => null;

   procedure Increment (X : in out Clock; Inc : Integer := 1) with
     Global => null;

   type Chronometer is new Clock with private;

   procedure Display_Value (X : Chronometer) with
     Global => null;

private

   type Instrument is abstract tagged
      record
         Name : String (1 .. 14) := "              ";
      end record;

   type Speedometer is new Instrument with
      record
         Value : Speed := 0;
      end record;

   type Gauge is new Instrument with
      record
         Value : Percent := 0;
      end record;

   type Graphic_Gauge is new Gauge with
      record
         Size  : Integer := 20;
         Fill  : Character := '*';
         Empty : Character := '.';
      end record;

   type Clock is new Instrument with
      record
         Seconds : Sixty := 0;
         Minutes : Sixty := 0;
         Hours : Twenty_Four := 0;
      end record;

   type Chronometer is new Clock with null record;
end Instr;
