package Simple
with SPARK_Mode
is

   type Shape_Kind_Type is (Square,
                            Triangle,
                            Circle);

   type Shape (Kind : Shape_Kind_Type) is record
      Name : String (1 .. 15);
      case Kind is
         when Square =>
            Side : Natural;
         when Triangle =>
            Side1 : Natural;
            Side2 : Natural;
            Side3 : Natural;
         when others =>
            Perimeter : Natural;
      end case;
   end record;

   procedure Test_Shape (S : Shape);

end Simple;
