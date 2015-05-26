with Types; use Types;

package Counter_Examples with
  SPARK_Mode
is

   --  from O220-024 (internal test)
   procedure Float_Last (X, Y : Float; Res : out Float);

   --  from O525-023 (crypto library)
   procedure Upper_Multiple_Of_64
     (B   :     Boolean;
      X   :     Unsigned_32;
      Res : out Unsigned_32);

end Counter_Examples;
