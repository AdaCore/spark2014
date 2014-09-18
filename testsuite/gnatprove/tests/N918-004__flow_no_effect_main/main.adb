with Text_IO;

procedure Main
  with SPARK_Mode
is

   --  The function below is intended to determine whether a given triangle
   --  (specified by the lengths of its three sides) is a right-angle triangle.
   --  The postcondition and the code have been made simpler by making a
   --  precondition on the caller that the longest side is given first.
   --  (Note that the function could have been implemented as a simple
   --  expression function.)

   function Is_Right_Angle_Triangle (Long_Side : Natural;
                                     Side_2    : Natural;
                                     Side_3    : Natural) return Boolean
     with Post => (if Long_Side * Long_Side =
                     (Side_2 * Side_2) + (Side_3 * Side_3)
                   then Is_Right_Angle_Triangle'Result = True)
   is
   begin
      -- Note that this function has multiple return statements. In SPARK 2005
      -- this was not permitted due to flow analysis restrictions, but these
      -- restrictions have been lifted in SPARK 2014.
      if Long_Side * Long_Side = (Side_2 * Side_2) + (Side_3 * Side_3) then
         return True;
      else
         return False;
      end if;
   end Is_Right_Angle_Triangle;

begin -- Main Program
   if Is_Right_Angle_Triangle (Natural'Last, Natural'Last, Natural'Last) then
      Text_IO.Put_Line ("Yes");
   else
      Text_IO.Put_Line ("False");
   end if;
end Main;
