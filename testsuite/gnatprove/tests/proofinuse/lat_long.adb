package body Lat_Long with SPARK_Mode is

   function Distance (Source, Destination : Coordinates) return Float_With_Approx
   is
      Delta_Lat : Float_With_Approx;
      Delta_Long : Float_With_Approx;
   begin
      Delta_Lat := (Destination.Lat - Source.Lat) * R * Conv_Deg_To_Rad;
      Delta_Long := (Destination.Long - Source.Long) * R / Cos(Source.Lat);
      return Sqrt(Delta_Lat * Delta_Lat + Delta_Long * Delta_Long);
   end Distance;

end Lat_Long;
