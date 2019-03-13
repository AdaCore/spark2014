
package body Camera_Motion with SPARK_Mode => On is

   --  Filters are expected to be indexed symetrically around zero in both dimensions.

   type Filter_Type is array (Integer range <>,
                              Integer range <>) of Integer
   with Dynamic_Predicate => Filter_Type'First (1) = -Filter_Type'Last (1) and
                             Filter_Type'First (2) = -Filter_Type'Last (2);


   type Image_Statistics_Type is record
      Min  : BW_Pixel;
      Max  : BW_Pixel;
      Mean : BW_Pixel;
      StdDev : BW_Pixel;
   end record;

   --
   function Sqrt (v : in Natural) return Natural is
      s_old : Integer := 10;  -- Initial guess
      s_new : Integer;
   begin
      for i in 1 .. 20 loop
         s_new := (s_old + (v / s_old)) / 2;
         exit when s_new = s_old or s_new = 0;
         s_old := s_new;
      end loop;
      return s_new;
   end Sqrt;

   --
   function Product_Sum (Filter : in Filter_Type;
                         Image  : in BW_Image_Type;
                         Col    : in Columns;
                         Row    : in Rows) return Integer is
      Sum  : Integer := 0;
      x, y : Integer;
   begin
      for Filter_Row in Filter'Range (1) loop
         y := Filter_Row + Integer (Row);
         if not (y in Image'Range (1)) then
            Sum := 0;
            exit;
         end if;

         for Filter_Col in Filter'Range (2) loop
            x := Filter_Col + Integer (Col);
            if not (x in Image'Range (2)) then
               Sum := 0;
               exit;
            end if;

            Sum := Sum + Filter (Filter_Row, Filter_Col) * Integer (Image (y, x));
         end loop;
      end loop;

      return Sum;
   end Product_Sum;

   --
   generic
      type Result_Type is range <>;
   function Clamp (Value : in Integer) return Result_Type;

   function Clamp (Value : in Integer) return Result_Type is
   begin
      if Value < Integer (Result_Type'First) then
         return Result_Type'First;
      end if;

      if Value > Integer (Result_Type'Last) then
         return Result_Type'Last;
      end if;

      return Result_Type (Value);
   end Clamp;

   --
   function Clamp_Pixel is new Clamp (Result_Type => BW_Pixel);

   --
   function Difference_Image (Image1 : in BW_Image_Type;
                              Image2 : in BW_Image_Type) return BW_Image_Type is
      v1, v2 : Integer;
   begin
      return Result : BW_Image_Type (Image1'Range (1), Image1'Range (2)) do
         for Row in Image1'Range (1) loop
            for Col in Image1'Range (2) loop
               v1 := Integer (Image1 (Row, Col));
               v2 := Integer (Image2 (Row, Col));
               Result (Row, Col) := Clamp_Pixel (abs (v1 - v2));
            end loop;
         end loop;
      end return;
   end Difference_Image;

   --
   function Square_Image (Image : in BW_Image_Type) return BW_Image_Type is
      v : Integer;
   begin
      return Result : BW_Image_Type (Image'Range (1), Image'Range (2)) do
         for Row in Image'Range (1) loop
            for Col in Image'Range (2) loop
               v := Integer (Image (Row, Col));
               Result (Row, Col) := Clamp_Pixel (v * v);
            end loop;
         end loop;
      end return;
   end Square_Image;

  --
   function Get_Image_Statistics (Image : in BW_Image_Type) return Image_Statistics_Type is
      v   : BW_Pixel;
      Min : BW_Pixel := BW_Pixel'Last;
      Max : BW_Pixel := BW_Pixel'First;
      Sum   : Natural := 0;
      Count : Natural := 0;
      Mean  : Natural;
      Var_Sum : Natural := 0;
   begin
      --  Get min and max values.
      for Row in Image'Range (1) loop
         for Col in Image'Range (2) loop
            v := Image (Row, Col);
            if v > Max then
               Max := v;
            end if;
            if v < Min then
               Min := v;
            end if;
            Sum := Sum + Natural (v);
            Count := Count + 1;
         end loop;
      end loop;

      Mean := Sum / Count;

      --  Get Variance and StdDev
      for Row in Image'Range (1) loop
         for Col in Image'Range (2) loop
            v := Image (Row, Col);
            Var_Sum := Var_Sum + (Integer (v) - Mean) ** 2;
         end loop;
      end loop;

      return Result : Image_Statistics_Type do
         Result.Min := Min;
         Result.Max := Max;
         Result.Mean := BW_Pixel (Mean);
         Result.StdDev := BW_Pixel (Sqrt (Var_Sum / Count));
      end return;
   end Get_Image_Statistics;

   --
   function Clip_Image (Threshold : in BW_Pixel;
                        Image     : in BW_Image_Type) return BW_Image_Type is
      v : BW_Pixel;
   begin
      return Result : BW_Image_Type (Image'Range (1), Image'Range (2)) do
         for Row in Image'Range (1) loop
            for Col in Image'Range (2) loop
               v := Image (Row, Col);
               if v < Threshold then
                  v := 0;
               end if;
               Result (Row, Col) := v;
            end loop;
         end loop;
      end return;
   end Clip_Image;

   --
   function Filter_Image (Filter : in Filter_Type;
                          Image : in BW_Image_Type) return BW_Image_Type is
      Low  : constant Integer := Integer (BW_Pixel'First);
      High : constant Integer := Integer (BW_Pixel'Last);
      Bias : constant Integer := (High - Low) / 2;
      Sum  : Integer;
   begin
      return Result : BW_Image_Type (Image'Range (1), Image'Range (2)) do
         for Row in Image'Range (1) loop
            for Col in Image'Range (2) loop
               Sum := Bias + Product_Sum (Filter, Image, Col, Row);
               Result (Row, Col) := Clamp_Pixel (Sum);
            end loop;
         end loop;
      end return;
   end Filter_Image;

   --
   function Measure_Motion (Ref_Image   : in BW_Image_Type;
                            New_Image   : in BW_Image_Type;
                            Column_From : in Columns;
                            Column_To   : in Columns;
                            Row_From    : in Rows;
                            Row_To      : in Rows) return Motion_Type is
      Edge_3x3 : constant Filter_Type (-1 .. 1, -1 .. 1) :=
        (
         (-1, 0, 1),
         (-2, 0, 2),
         (-1, 0, 1)
        );
      Erode_3x3 : Filter_Type (-1 .. 1, -1 .. 1) :=
        (
         (1, 1, 1),
         (1, 1, 1),
         (1, 1, 1)
        );

      type Natural_64 is range 0 .. (2**63 - 1);

      Edge_Ref     : BW_Image_Type (Ref_Image'Range (1), Ref_Image'Range (2));
      Edge_New     : BW_Image_Type (New_Image'Range (1), New_Image'Range (2));
      Diff_Image   : BW_Image_Type (New_Image'Range (1), New_Image'Range (2));
      Result_Image : BW_Image_Type (Ref_Image'Range (1), Ref_Image'Range (2));

      Diff     : Integer;
      vx, vy   : Integer;
      Diff_Sum : Integer := 0;
      Weighted_Sum_X  : Integer := 0;
      Weighted_Sum_Y  : Integer := 0;
      Sum_Weights     : Integer := 0;
      Weighted_Mean_X : Integer := 0;
      Weighted_Mean_Y : Integer := 0;
      Weighted_Var_X  : Natural_64 := 0;
      Weighted_Var_Y  : Natural_64 := 0;
      Weighted_Stddev_X : Integer := 0;
      Weighted_Stddev_Y : Integer := 0;
      Stats : Image_Statistics_Type;
   begin
      --  Find horizontal edges on both images (Sobel matrix).
      Edge_Ref := Filter_Image (Edge_3x3, Ref_Image);
      Edge_New := Filter_Image (Edge_3x3, New_Image);

      --  Find the absolute differences.
      Diff_Image := Difference_Image (Edge_Ref, Edge_New);

      --  Get Statistics of differences..
      Stats := Get_Image_Statistics (Diff_Image);

      --  Keep only highest values (>= Mean + StdDev).
      Result_Image := Clip_Image (Stats.Mean + Stats.StdDev, Diff_Image);

      --  Calculate Weighted means for each axis.
      for Row in Row_From .. Row_To loop
         for Col in Column_From .. Column_To loop
            Diff := Integer (Result_Image (Row, Col));
            Diff_Sum := Diff_Sum + Diff;

            Sum_Weights := Sum_Weights + Diff;
            Weighted_Sum_X := Weighted_Sum_X + (Integer (Col) * Diff);
            Weighted_Sum_Y := Weighted_Sum_Y + (Integer (Row) * Diff);
         end loop;
      end loop;

      if Sum_Weights = 0 then
         Weighted_Mean_X := (Integer (Ref_Image'Last (2)) - Integer (Ref_Image'First (2))) / 2;
         Weighted_Mean_Y := (Integer (Ref_Image'Last (1)) - Integer (Ref_Image'First (1))) / 2;
      else
         Weighted_Mean_X := Weighted_Sum_X / Sum_Weights;
         Weighted_Mean_Y := Weighted_Sum_Y / Sum_Weights;
      end if;

      --  Calculate weighted variances for each axis.
      for Row in Row_From .. Row_To loop
         for Col in Column_From .. Column_To loop
            vx := abs (Integer (Col) - Weighted_Mean_X);
            vy := abs (Integer (Row) - Weighted_Mean_Y);

            Weighted_Var_X := Weighted_Var_X +
              Natural_64 (vx * vx * Integer (Result_Image (Row, Col)));
            Weighted_Var_Y := Weighted_Var_Y +
              Natural_64 (vy * vy * Integer (Result_Image (Row, Col)));
         end loop;
      end loop;

      if Sum_Weights = 0 then
         Weighted_Var_X := 0;
         Weighted_Var_Y := 0;
      else
         Weighted_Var_X := Weighted_Var_X / Natural_64 (Sum_Weights);
         Weighted_Var_Y := Weighted_Var_Y / Natural_64 (Sum_Weights);
      end if;

      --  Calculate weighted standard deviation for each axis.
      Weighted_Stddev_X := Sqrt (Integer (Weighted_Var_X));
      Weighted_Stddev_Y := Sqrt (Integer (Weighted_Var_Y));

      --  Report
      return Motion : Motion_Type do
         Motion.Level      := Diff_Sum;
         Motion.Center_Col := Weighted_Mean_X;
         Motion.Center_Row := Weighted_Mean_Y;
         Motion.StdDev_Col := Weighted_Stddev_X;
         Motion.StdDev_Row := Weighted_Stddev_Y;
      end return;
   end Measure_Motion;

end Camera_Motion;
