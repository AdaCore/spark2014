package Predicate_Ints
  with SPARK_Mode
is
   pragma Elaborate_Body;
   type Int is tagged record
      Min, Max, Value : Integer;
   end record;
 --    with Predicate => Value in Min .. Max;

   function Equal (Arg1, Arg2 : Int) return Boolean;
   procedure Bump (Arg : in out Int) with
     Pre'Class  => Arg.Value < Arg.Max - 10,
     Post'Class => Arg.Value > Arg.Value'Old;
   procedure Display (Arg : Int; Msg : String := "") with Global => null;
   function "+" (Arg1, Arg2 : Int) return Int with
     Pre'Class => Arg1.Min = Arg2.Min and Arg1.Max = Arg2.Max;
   procedure Reset (Arg : out Int) with Extensions_Visible;
   function Zero return Int;

   procedure Call_Bump (Arg : in out Int'Class) with
     Pre  => Arg.Value < Arg.Max - 10,
     Post => Arg.Value > Arg.Value'Old;

   type Approx_Int is new Int with record
      Precision : Natural;
   end record;

   overriding function Equal (Arg1, Arg2 : Approx_Int) return Boolean;
   overriding procedure Bump (Arg : in out Approx_Int);
   --  inherited Pre'Class and Post'Class
   overriding procedure Display (Arg : Approx_Int; Msg : String := "") with
     Global => null;
   function "+" (Arg1, Arg2 : Approx_Int) return Approx_Int;
   overriding function Zero return Approx_Int;

   not overriding procedure Blur (Arg : in out Approx_Int);

end Predicate_Ints;
