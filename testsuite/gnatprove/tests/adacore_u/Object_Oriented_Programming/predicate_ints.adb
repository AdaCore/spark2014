with Ada.Text_IO; use Ada.Text_IO;

package body Predicate_Ints
  with SPARK_Mode
is

   function Equal (Arg1, Arg2 : Int) return Boolean is
      (Arg1.Value = Arg2.Value);

   procedure Bump (Arg : in out Int) is
   begin
      Arg.Value := Arg.Value + 1;
   end Bump;

   procedure Display (Arg : Int; Msg : String := "") with
     SPARK_Mode => Off
   is
   begin
      if Msg /= "" then
         Put (Msg & " - ");
      end if;
      Put_Line ("Int is ( Min =" & Integer'Image(Arg.Min) &
                  ", Max =" & Integer'Image(Arg.Max) &
                  ", Value =" & Integer'Image(Arg.Value) & " )");
   end Display;

   function "+" (Arg1, Arg2 : Int) return Int is
   begin
      return Int'(Min   => Arg1.Min,
                  Max   => Arg1.Max,
                  Value => Arg1.Value + Arg2.Value);
   end "+";

   procedure Reset (Arg : out Int) is
   begin
      Int'Class(Arg) := Int'(Zero);
   end Reset;

   function Zero return Int is (Int'(Min => -100, Max => 100, Value => 0));

   procedure Call_Bump (Arg : in out Int'Class) is
   begin
      Arg.Bump;
   end Call_Bump;

   procedure Re_Call_Bump (Arg : in out Int) with
     Extensions_Visible,
     Pre  => Arg.Value < Arg.Max - 10,
     Post => Arg.Value > Arg.Value'Old
   is
   begin
      Int'Class(Arg).Bump;
   end Re_Call_Bump;

   overriding function Equal (Arg1, Arg2 : Approx_Int) return Boolean is
      (abs (Arg1.Value - Arg2.Value) <= Arg1.Precision + Arg2.Precision);

   overriding procedure Bump (Arg : in out Approx_Int) is
   begin
      Arg.Value := Arg.Value + 10;
   end Bump;

   overriding procedure Display (Arg : Approx_Int; Msg : String := "") with
     SPARK_Mode => Off
   is
   begin
      if Msg /= "" then
         Put (Msg & " - ");
      end if;
      Put_Line ("Int is ( Min =" & Integer'Image(Arg.Min) &
                  ", Max =" & Integer'Image(Arg.Max) &
                  ", Value =" & Integer'Image(Arg.Value) &
                  ", Precision =" & Integer'Image(Arg.Precision) & " )");
   end Display;

   function "+" (Arg1, Arg2 : Approx_Int) return Approx_Int is
   begin
      return (Int(Arg1) + Int(Arg2) with Precision =>
                Integer'Max (Arg1.Precision, Arg2.Precision));
   end "+";

   function Zero return Approx_Int is (Int'(Zero) with Precision => 0);

   not overriding procedure Blur (Arg : in out Approx_Int) is
   begin
      Arg.Precision := Arg.Precision + 1;
   end Blur;

end Predicate_Ints;
