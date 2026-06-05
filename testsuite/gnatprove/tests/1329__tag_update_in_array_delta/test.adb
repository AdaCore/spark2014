pragma Ada_2022;
pragma Extensions_Allowed (On);

procedure Test with SPARK_Mode is

   type Root is tagged record
      F : Integer;
   end record;

   type Holder is array (Positive range 1 .. 2) of Root;

   H : Holder := (1 .. 2 => (F => 0));
   Y : Holder := (H with delta 1 => (F => 3));
begin
   null;
end;
