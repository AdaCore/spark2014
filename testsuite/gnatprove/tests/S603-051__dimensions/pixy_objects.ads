with Dimensions;
with Camera_Types;

package Pixy_Objects with SPARK_Mode => On is
   use Dimensions;

   subtype Distance_To_Object_Range is Dimensions.Length range 0.0 * cm .. 1.0 * m;

   type Object_Type is
     (Orange, Green, Yellow, Golfball, Port);

   type Closest_Objects_Type is array (Object_Type) of Camera_Types.Blob_Type;
   type Objects_Found_Type is array (Object_Type) of Boolean;

   procedure Detect_Objects (Blobs         : in  Camera_Types.Blob_Array_Type;
                             Objects_Found : out Objects_Found_Type;
                             Objects       : out Closest_Objects_Type);

   function Distance_To_Object (Object_Blob : Camera_Types.Blob_Type) return Distance_To_Object_Range;
   function Heading_Error_To_Object (Object_Blob : Camera_Types.Blob_Type) return Dimensions.Normalized_Angle;
   function Width_Of_Object (Object_Blob : Camera_Types.Blob_Type) return Non_Negative_Short_Length;

   --  Convenience functions.
   function More_Centered (This_Blob : in Camera_Types.Blob_Type;
                           Than_Blob : in Camera_Types.Blob_Type) return Boolean;

   --  Returns size of row in cm.
   function Size_At_Row (Pixel_Size : in Camera_Types.Widths;
                         Row        : in Camera_Types.Rows) return Float
   with Post => Size_At_Row'Result >= 0.0 and Size_At_Row'Result <= 1000.0;

end Pixy_Objects;
