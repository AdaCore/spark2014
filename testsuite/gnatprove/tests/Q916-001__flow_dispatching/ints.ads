package Ints
  with SPARK_Mode
is

   type Int is tagged record
      Min, Max, Value : Integer;
   end record;

   function Equal (Arg1, Arg2 : Int) return Boolean;
   procedure Bump (Arg : in out Int) with
     Pre'Class  => Arg.Value < Arg.Max - 10,
     Post'Class => Arg.Value > Arg.Value'Old;
   procedure Display (Arg : Int; Msg : String := "");

   procedure Call_Bump (Arg : in out Int'Class) with
     Pre  => Arg.Value < Arg.Max - 10,
     Post => Arg.Value > Arg.Value'Old;

   type Approx_Int is new Int with record
      Precision : Natural;
   end record;

   G : Integer;

   overriding function Equal (Arg1, Arg2 : Approx_Int) return Boolean;
   overriding procedure Bump (Arg : in out Approx_Int);
   --  inherited Pre'Class and Post'Class
   overriding procedure Display (Arg : Approx_Int; Msg : String := "");

   not overriding procedure Blur (Arg : in out Approx_Int);

end Ints;
