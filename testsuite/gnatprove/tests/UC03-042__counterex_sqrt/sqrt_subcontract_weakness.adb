function Sqrt_Subcontract_Weakness (N : Natural) return Natural
with
  Pre  => N <= 10_000,
  Post => Sqrt_Subcontract_Weakness'Result*Sqrt_Subcontract_Weakness'Result <= N
    and then N < (Sqrt_Subcontract_Weakness'Result+1)*(Sqrt_Subcontract_Weakness'Result+1)
is
   R : Natural := N;
   Y : Integer := N*N;
   Z : Integer := (-2)*N+1;
begin
   while Y > N loop
      pragma Loop_Invariant (R <= N);
      pragma Loop_Invariant (Y = R*R);
      pragma Loop_Invariant (N < (R+1)*(R+1));
      --  suppress pragma Loop_Invariant (Z = (-2)*R+1);

      Y := Y+Z;
      Z := Z+2;
      R := R-1;
   end loop;

   return R;
end Sqrt_Subcontract_Weakness;
