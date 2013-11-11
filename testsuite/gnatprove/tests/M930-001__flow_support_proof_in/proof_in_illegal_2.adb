package body Proof_In_Illegal_2
  with SPARK_Mode,
       Refined_State => (State => Body_Var)
is
   Body_Var : Integer := 1;

   procedure Error_Derived_From_Proof_In (X : in out Integer)
     with Refined_Global => (Proof_In => Body_Var)
   is
      Temp : Integer := 1;
   begin
      for I in 1 .. 10 loop
         if X < 0 then
            if X + 1 < -5 then
               Temp := X + 2;
            else
               if X = 5 then
                  Temp := 10;
               else
                  Temp := Body_Var + 1;
               end if;
            end if;
         else
            Temp := Body_Var - 1;
         end if;
      end loop;
      X := Temp;  --  Error, derived output from Proof_In.
   end Error_Derived_From_Proof_In;
end Proof_In_Illegal_2;
