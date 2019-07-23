with Gnat.Io; use Gnat.Io;
package body Instr is

   procedure Set_Name (X : in out Instrument; S : String) is
   begin
      for J in S'Range loop
         X.Name (J) := S (J);
         exit when J >= X.Name'Last;
      end loop;
   end Set_Name;

   procedure Display_Value (X : Instrument) is
   begin
      New_Line;
      Put (X.Name);
      Put (" : ");
   end Display_Value;

   procedure Display_Value (X : Speedometer) is
   begin
      Instrument (X).Display_Value;
      Put (X.Value);
      Put (" Miles per Hour");
   end Display_Value;

   procedure Set   (X : in out Speedometer'Class; V : Speed) is
   begin
      X.Value := V;
   end Set;

   function Value (X : Speedometer'Class) return Speed is
   begin
      return X.Value;
   end Value;

   procedure Display_Value (X : Gauge) is
   begin
      Instrument (X).Display_Value;
      Put (X.Value);
      Put (" %");
   end Display_Value;

   procedure Set (X : in out Gauge'Class; V : Percent) is
   begin
      X.Value := V;
   end Set;

   function Value (X : Gauge'Class) return Percent is
   begin
      return X.Value;
   end Value;

   procedure Display_Value (X : Graphic_Gauge) is
      Lg : constant Integer := X.Size * X.Value / 100;
      S1 : constant String (1 .. Lg) := (others => X.Fill);
      S2 : constant String (Lg + 1 .. X.Size) := (others => X.Empty);
   begin
      Instrument (X).Display_Value;
      Put ('<');
      Put (S1);
      Put (S2);
      Put ('>');
   end Display_Value;

   procedure Display_Value (X : Clock) is
   begin
      Instrument (X).Display_Value;
      Put (Character'Val (Character'Pos ('0') + X.Hours / 10));
      Put (Character'Val (Character'Pos ('0') + X.Hours mod 10));
      Put (":");
      Put (Character'Val (Character'Pos ('0') + X.Minutes / 10));
      Put (Character'Val (Character'Pos ('0') + X.Minutes mod 10));
      Put (":");
      Put (Character'Val (Character'Pos ('0') + X.Seconds / 10));
      Put (Character'Val (Character'Pos ('0') + X.Seconds mod 10));
   end Display_Value;

   procedure Increment (X : in out Clock; Inc : Integer := 1) is
      nInc : Integer;

   begin
      X.Seconds := (X.Seconds + Inc) mod 60;
      nInc := (X.Seconds + Inc) / 60;
      X.Minutes := (X.Minutes + nInc) mod 60;
      nInc := (X.Minutes + nInc) / 60;
      X.Hours := (X.Hours + nInc) mod 24;
   end Increment;

   procedure Init (X : in out Clock'Class;
                   H : Twenty_Four := 0;
                   M, S : Sixty := 0) is
   begin
      X.Seconds := S;
      X.Minutes := M;
      X.Hours := H;
   end Init;

   function Seconds (X : Clock'Class) return Sixty is
   begin
      return X.Seconds;
   end Seconds;

   procedure Display_Value (X : Chronometer) is
      V : Integer;
   begin
      Instrument (X).Display_Value;

      V := X.Seconds + X.Minutes * 60 + X.Hours * 3600;

      Put ("<<");
      Put (Character'Val (Character'Pos ('0') + (V / 1000) mod 10));
      Put (Character'Val (Character'Pos ('0') + (V / 100) mod 10));
      Put (Character'Val (Character'Pos ('0') + (V / 10) mod 10));
      Put (Character'Val (Character'Pos ('0') + V mod 10));
      Put (">>");
   end Display_Value;

end Instr;
