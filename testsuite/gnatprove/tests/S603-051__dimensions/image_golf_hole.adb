with Dimensions;
with Pixy_Objects;

package body Image_Golf_Hole with SPARK_Mode => On is

   use Camera_Types;

   subtype Scan_Rows    is Rows    range 70 .. 140;
   subtype Scan_Columns is Columns range 60 .. 260;


   procedure Process_Image (Image : in Camera_Types.BW_Image_320_Type) is

      procedure Set_Position (Col : in Columns;
                              Row : in Rows) is
         Blob              : Camera_Types.Blob_Type;
         Observed_Distance : Dimensions.Short_Length;
      begin
         Blob := (signature => 7,
                  x         => Col,
                  y         => Row,
                  width     => 1,
                  height    => 1);
         Observed_Distance := Pixy_Objects.Distance_To_Object (Object_Blob => Blob);
      end Set_Position;


      --
      Best_Column : Columns := 0;
      Best_Row    : Scan_Rows := Scan_Rows'First;
   begin
         Set_Position (Best_Column, Best_Row);

   end Process_Image;

end Image_Golf_Hole;
