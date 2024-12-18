package body Exit_Cases_Incomplete with SPARK_Mode is

   procedure Might_Return_Abnormally (X : in out Integer) is
   begin
      case X is
      when 1 =>
         X := 3;
      when 2 =>
         raise E1;
      when others =>
         raise E2;
      end case;
   end Might_Return_Abnormally;

end Exit_Cases_Incomplete;
