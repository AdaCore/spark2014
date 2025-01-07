package body Exit_Cases_Non_Terminating with SPARK_Mode is

   procedure Might_Return_Abnormally (X : in out Integer) is
   begin
      loop
         null;
      end loop;
   end Might_Return_Abnormally;

end Exit_Cases_Non_Terminating;
