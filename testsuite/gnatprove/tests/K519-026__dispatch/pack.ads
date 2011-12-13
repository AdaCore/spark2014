package Pack is

   type Root is tagged null record;

   type Child is new Root with null record;

   procedure Proc (P: in out Child);

end Pack;
