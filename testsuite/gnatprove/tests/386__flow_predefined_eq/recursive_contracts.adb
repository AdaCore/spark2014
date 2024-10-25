procedure Recursive_Contracts with SPARK_Mode is
   type Rec_1 is record A : Integer; end record;
   subtype Subrec_1 is Rec_1;

   type Rec_2 is record B : Integer; end record;

   function "=" (Left, Right : Rec_1) return Boolean
   is (True and Left.A = Right.A)
   with Post => "="'Result = (F (Left) = F (Right));

   function F (R : Rec_1) return Rec_2
   is (Rec_2'(B => R.A))
   with Post => Subrec_1' (A => F'Result.B) = Subrec_1'(R);

begin
   null;
end Recursive_Contracts;
