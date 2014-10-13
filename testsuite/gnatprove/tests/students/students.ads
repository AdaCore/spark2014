with Dates;

package Students
  with SPARK_Mode => On
is
   type Gender_Type is (Male, Female, Unspecified);
   type Meal_Plan_Type is (None, On_Demand, Basic, Full);
   type Student_ID is range 0 .. 999_999;
   subtype Valid_Student_ID is Student_ID range 1 .. Student_ID'Last;

   type GPA_Type is delta 0.01 range 0.00 .. 4.00;
   type Money_Type is delta 0.01 range -99_999.99 .. +99_999.99;

   type Student_Record is private;

   -- Adjusts the tuition based on student characteristics.
   function Compute_Bill (Student : Student_Record;
                          Base_Tuition : Money_Type) return Money_Type
   with
     Pre => (0.00 <= Base_Tuition and Base_Tuition < 20_000.00);

private
   type Student_Record is record
      Birth_Date: Dates.Date;
      ID : Student_ID;
      Gender : Gender_Type;
      GPA : GPA_Type;
      Part_Time : Boolean;
      In_State : Boolean;
      Resident : Boolean;
      Meal_Plan : Meal_Plan_Type;
      Self_Insured : Boolean;
   end record;
end Students;
