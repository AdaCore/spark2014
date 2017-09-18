package Abstract_Ints
  with SPARK_Mode
is

   type Int is tagged private;

   function Equal (Arg1, Arg2 : Int) return Boolean;
   function Get_Value (Arg : Int) return Integer;
   function Small (Arg : Int) return Boolean; -- with Ghost;
   procedure Bump (Arg : in out Int) with
     Pre'Class  => Arg.Small,
     Post'Class => Arg.Get_Value > Arg.Get_Value'Old;
   procedure Display (Arg : Int; Msg : String := "") with Global => null;

   procedure Call_Bump (Arg : in out Int'Class) with
     Pre  => Arg.Small,
     Post => Arg.Get_Value > Arg.Get_Value'Old;

   type Approx_Int is new Int with private;

   overriding function Equal (Arg1, Arg2 : Approx_Int) return Boolean;
   overriding function Small (Arg : Approx_Int) return Boolean; -- with Ghost;
   overriding procedure Bump (Arg : in out Approx_Int);
   --  inherited Pre'Class and Post'Class
   overriding procedure Display (Arg : Approx_Int; Msg : String := "") with
     Global => null;

   not overriding procedure Blur (Arg : in out Approx_Int);

private
   type Int is tagged record
      Min, Max, Value : Integer;
   end record;

   type Approx_Int is new Int with record
      Precision : Natural;
   end record;

   function Get_Value (Arg : Int) return Integer is (Arg.Value);
   function Small (Arg : Int) return Boolean is (Arg.Value < Arg.Max - 10);
   function Small (Arg : Approx_Int) return Boolean is (Arg.Value in 1 .. 100);

end Abstract_Ints;
