with Ada.Numerics, Ada.Numerics.Elementary_Functions;
use Ada.Numerics, Ada.Numerics.Elementary_Functions;

package Lat_Long with SPARK_Mode is

   type Float_With_Approx is new Float;
   function "<" (Left, Right: Float_With_Approx) return Boolean is
     (Float(Left) < Float(Right) + 10.0E-6);

   R : constant Float_With_Approx := 6_367_444.7;
   Conv_Deg_To_Rad : constant Float_With_Approx := Pi / 180.0;

   function Cos(X : Float_With_Approx) return Float_With_Approx
   is (Float_With_Approx(Sin(Float(X)))) with
   Post => (if X in -75.0 .. 75.0 then Cos'Result >= 0.1);

   function Sqrt(X : Float_With_Approx) return Float_With_Approx
   is (Float_With_Approx(Sqrt(Float(X))));

   subtype Latitude is Float_With_Approx range - 75.0 .. 75.0;
   subtype Longitude is Float_With_Approx range Float_With_Approx'Succ(- 180.0) .. 180.0;

   type Coordinates is record
      Lat : Latitude;
      Long : Longitude;
   end record;

   function Distance(Source, Destination : Coordinates) return Float_With_Approx with
     Post => Distance'Result = Sqrt(
               Delta_Lat_In_Meters(Source, Destination) *  Delta_Lat_In_Meters(Source, Destination) +
               Delta_Long_In_Meters(Source, Destination) * Delta_Long_In_Meters(Source, Destination));

   function Delta_Lat_In_Meters(Source, Destination : Coordinates) return Float_With_Approx
   is ((Destination.Lat - Source.Lat) * R * Conv_Deg_To_Rad)
   with Ghost,
     Post => abs(Delta_Lat_In_Meters'Result) < (Pi * R);

   function Delta_Long_In_Meters(Source, Destination : Coordinates) return Float_With_Approx
   is ((Destination.Long - Source.Long) * R / Cos(Source.Lat))
   with Ghost,
     Post => abs(Delta_Long_In_Meters'Result) < (2.0 * Pi * R);

end Lat_Long;
