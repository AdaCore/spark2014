package Repro with SPARK_Mode is

   type Sp is range 1 .. 14;
   type T is range 1 .. 31;

   type Kind is (Kind0, Kind1, Kind2);

   type Item (K : Kind := Kind0) is record
      case K is
         when Kind0 =>
            XX : Integer := 1;
         when Kind1 =>
            YY : Integer := 1;
         when Kind2 =>
            ZZ : Integer := 1;
      end case;
   end record;

   type Speed_Map is array (Sp range <>) of Item;

   type Speed (Len : Sp := 1) is record
      M : Speed_Map (1 .. Len);
   end record;

   type SSP (B : Boolean := False) is record
      case B is
         when True =>
            S : Speed;
         when False =>
            null;
      end case;
   end record;

   type A is array (T range <>) of SSP;

   type R (Y : T := 1) is record
      X : A(1 .. Y);
   end record;

   procedure Process (Arg : R);

end Repro;
