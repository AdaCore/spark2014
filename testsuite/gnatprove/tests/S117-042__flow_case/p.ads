package P is
   type Single is (One);
   procedure Effect1 (B : Boolean; E : Single; Y : out Integer) with Global => null;
   procedure Effect2 (B : Boolean; E : Single; Y : out Integer) with Global => null;
end;
