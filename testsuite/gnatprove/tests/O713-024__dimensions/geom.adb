package body Geom with SPARK_Mode is

   function Angle_Normalize (A : Angle) return Angle is
      Ret : Angle := A;
   begin
      while Ret > 3.14 loop
         Ret := Ret - 2.0;
      end loop;
      return Ret;
   end Angle_Normalize;

end Geom;
