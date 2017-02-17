with Ada.Text_IO; use Ada.Text_IO;

package body Power_and_Sum is pragma SPARK_Mode (On);
   procedure Power(X : in Integer; N : in Positive; Result: out Integer) is
      I : Integer := 1;
   begin
      Result := X;
      while I < N loop
         pragma Loop_Invariant (Result = X ** I and then (I >= 1));
         Result := Result * X;
         I := I + 1;
      end loop;
   end Power;

   procedure Sum(N : in Positive; Result: out Positive) is
      I : Positive := 1;
      TotalSum : Natural := 0;
   begin
      while I <= N loop
         pragma Loop_Invariant (2*TotalSum = I*(I-1));

         TotalSum := TotalSum + I;
         I := I + 1;
      end loop;
      pragma Assert (2*TotalSum = N*(N+1));
      Result := TotalSum;
   end Sum;

   procedure Sum_Of_Sum(N : in Positive; Result: out Positive) is
      I : Positive := 1;
      J : Positive := 1;
      TotalSum : Natural := 0;
      InnerSum : Natural := 0;
   begin
      while I <= N loop
         pragma Loop_Invariant (6*TotalSum = (I-1)*I*(I+1));

         InnerSum := 0;
         J := 1;
         while J <= I loop
            pragma Loop_Invariant (2*InnerSum = J*(J-1));

            InnerSum := InnerSum + J;
            J := J + 1;
         end loop;
         pragma Assert (J = I + 1);
      	 pragma Assert (2*InnerSum = I*(I+1));
         TotalSum := TotalSum + InnerSum;
         I := I + 1;
      end loop;
      pragma Assert (6*TotalSum = N*(N+1)*(N+2));
      Result := TotalSum;
   end Sum_Of_Sum;

end Power_and_Sum;
