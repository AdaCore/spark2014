package body Students
  with SPARK_Mode => On
is
   function Compute_Bill (Student : Student_Record;
                          Base_Tuition : Money_Type) return Money_Type is
      Tuition : Money_Type;
      Fees : Money_Type;
      Grants : Money_Type := 0.00;
      Insurance : Money_Type := 0.00;
      Two : Money_Type := 2.0;
   begin
      Tuition := Base_Tuition;

      if not Student.In_State then
         Tuition := Tuition + Tuition/2;
      end if;

      if not Student.Self_Insured then
         Insurance := 1_000.00;
      end if;

      if Student.Part_Time then
         Fees := 100.00;
      else
         Fees := 500.00;
      end if;

      if Student.Resident then
         Fees := Fees + 4_000.00;
         case Student.Meal_Plan is
            when None => null;
            when On_Demand => Fees := Fees + 100.00;
            when Basic => Fees := Fees + 1_000.00;
            when Full => Fees := Fees + 3_000.00;
         end case;
      else
         case Student.Meal_Plan is
            when None => null;
            when On_Demand => Fees := Fees + 200.00;
            when Basic => Fees := Fees + 1_500.00;
            when Full => Fees := Fees + 4_500.00;
         end case;
      end if;

      if Student.GPA >= 3.00 then
         Grants := Grants + 250.00;

         if Student.GPA >= 3.75 and Student.Gender = Female then
            Grants := Grants + 250.00;
         end if;
      end if;

      return (( Tuition + Fees) - Grants) + Insurance;
   end Compute_Bill;
end Students;
