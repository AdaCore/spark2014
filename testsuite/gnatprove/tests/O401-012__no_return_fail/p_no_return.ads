package p_no_return with SPARK_Mode is
   procedure Returning;
   pragma No_Return (Returning);
   procedure Difficult_Non_Returning (C : Natural);
   pragma No_Return (Difficult_Non_Returning);
end p_no_return;
