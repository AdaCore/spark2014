package Types is

   type Index is range 1 .. 8;

   type Array_1D is array (Index) of Integer;
   type Array_2D is array (Index, Index) of Integer;
   type Array_3D is array (Natural range 1 .. 5,
                           Natural range 1 .. 5,
                           Natural range 1 .. 5) of Integer;

   type My_Range is range 1 .. 10;

   type Rec is record
      S1 : Integer;
      S2 : Natural;
      S3 : My_Range;
   end record;

end Types;

