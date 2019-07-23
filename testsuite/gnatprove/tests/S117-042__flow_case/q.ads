package Q is
   type Triple is (One,Two,Three);
   subtype Single1 is Triple range One .. One;
   subtype Single2 is Triple range Two .. Two;
   subtype Single3 is Triple range Three .. Three;
   subtype Single4 is Triple with Static_Predicate => Single4 in One;
   subtype Single5 is Triple with Static_Predicate => Single5 = Two;
   subtype Single6 is Triple with Static_Predicate => Single6 in Three .. Three;

   procedure Effect1 (B : Boolean; E : Single1; Y : out Integer) with Global => null;
   procedure Effect2 (B : Boolean; E : Single2; Y : out Integer) with Global => null;
   procedure Effect3 (B : Boolean; E : Single3; Y : out Integer) with Global => null;
   procedure Effect4 (B : Boolean; E : Single4; Y : out Integer) with Global => null;
   procedure Effect5 (B : Boolean; E : Single5; Y : out Integer) with Global => null;
   procedure Effect6 (B : Boolean; E : Single6; Y : out Integer) with Global => null;

   procedure Effect0 (B : Boolean; E : Triple;  Y : out Integer) with Global => null;
   procedure Effect7 (B : Boolean; E : Triple;  Y : out Integer) with Global => null;

   procedure EffectD (B : Boolean; E : Triple;  Y : out Integer) with Depends => (Y => (B, E));
end;
