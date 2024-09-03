procedure Recursive_Contracts_Import with SPARK_Mode is
   type Rec_1 is record A : Integer; end record;
   subtype Subrec_1 is Rec_1;

   type Rec_2 is record B : Integer; end record;

   function "=" (Left, Right : Rec_1) return Boolean
   with Import,
        Post => "="'Result = (F (Left) = F (Right));

   function F (R : Rec_1) return Rec_2
   with Import,
        Post => Subrec_1' (A => F'Result.B) = Subrec_1'(R);

begin
   null;
end Recursive_Contracts_Import;
