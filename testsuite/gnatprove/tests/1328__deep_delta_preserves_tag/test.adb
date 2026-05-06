pragma Ada_2022;
pragma Extensions_Allowed (On);

procedure Test with SPARK_Mode is
   type Int_Arr is array (Positive range 1 .. 10) of Integer;

   type Root is tagged record
      F : Int_Arr;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   X : Root'Class := Root'Class (Child'(F => (others => 1), G => 2));
begin
   pragma Assert ((X with delta F => (others => 3)) in Child'Class);
   pragma Assert (Child ((X with delta F => (others => 3))).G = 2);
   pragma Assert ((X with delta F (1) => 1) in Child'Class);
   pragma Assert (Child ((X with delta F (1) => 1)).G = 2);
end;
