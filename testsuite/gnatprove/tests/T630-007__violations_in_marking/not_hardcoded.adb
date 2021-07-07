procedure Not_Hardcoded with SPARK_Mode is
   package Big_Integers is
      function Id (X : Integer) return Integer is (X);
   end Big_Integers;
   package Big_Numbers is
      package Big_Integers is
         function Id (X : Integer) return Integer is (X);
      end Big_Integers;
   end Big_Numbers;
   package Numerics is
      package Big_Numbers is
         package Big_Integers is
            function Id (X : Integer) return Integer is (X);
         end Big_Integers;
      end Big_Numbers;
   end Numerics;
   package Ada is
      package Numerics is
         package Big_Numbers is
            package Big_Integers is
               function Id (X : Integer) return Integer is (X);
            end Big_Integers;
         end Big_Numbers;
      end Numerics;
   end Ada;

   X : Integer := 1;
begin
   X := Big_Integers.Id (X);
   X := Big_Numbers.Big_Integers.Id (X);
   X := Numerics.Big_Numbers.Big_Integers.Id (X);
   X := Ada.Numerics.Big_Numbers.Big_Integers.Id (X);
end Not_Hardcoded;
