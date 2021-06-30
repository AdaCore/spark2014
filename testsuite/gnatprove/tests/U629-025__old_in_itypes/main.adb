with Ada.Strings.Fixed; use Ada.Strings.Fixed;
procedure Main with SPARK_Mode is
   procedure Erase
     (Source : in out String;
      N      : in out Positive)
   with
     Pre  => N <= Source'Length,
     Post => Source (N .. N) = (N'Old => ' ')
   is
   begin
      N := N - 1 + Source'First;
      Source (N) := ' ';
   end Erase;

   procedure Erase_2
     (Source : in out String;
      N      : in out Positive)
   with
     Pre  => N <= Source'Length,
     Post => N = N'Old - 1 + Source'First
     and then Source (Source'First .. N) = (1 .. N'Old => ' ')
     and then (if Source'Last > N then Source (N + 1 .. Source'Last) = Source'Old (N + 1 .. Source'Last))
   is
   begin
      Source := Overwrite (Source, Source'First, N * ' ');
      N := N - 1 + Source'First;
   end Erase_2;

begin
   null;
end;
