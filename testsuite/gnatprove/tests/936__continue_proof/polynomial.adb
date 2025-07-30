pragma Extensions_Allowed (All_Extensions);
procedure Polynomial with SPARK_Mode is
   type Var is new Integer;
   type Monomial_Base is array (Integer range <>) of Var;
   subtype Monomial is Monomial_Base with Predicate => Monomial'Last < Integer'Last;
   type Ring is mod 2**8;
   type AMonomial is access Monomial;
   type Coefficiented_Monomial is record
      Coeff : Ring;
      Mono  : not null AMonomial;
   end record;
   type Polynomial_Base is array (Integer range <>) of Coefficiented_Monomial;
   subtype Polynomial is Polynomial_Base with Predicate => Polynomial'Last < Integer'Last;
   function Eval_Var (V : Var) return Ring with Import, Global => null;
   function Eval_Monomial_Range (M : Monomial; I, J : Integer) return Ring
   is (if J <= I
       then 1
       else Eval_Var (M (I)) * Eval_Monomial_Range (M, I+1, J))
     with Subprogram_Variant => (Increases => I),
       Pre => M'First <= I and then J <= M'Last + 1;
   function Eval_Monomial (M : Monomial) return Ring
   is (Eval_Monomial_Range (M, M'First, M'Last + 1));

   function Eval_Polynomial_Range (P : Polynomial; I, J : Integer) return Ring
   is (if J <= I
       then 0
       else P(I).Coeff * Eval_Monomial (P (I).Mono.all)
            + Eval_Polynomial_Range (P, I+1, J))
     with Subprogram_Variant => (Increases => I),
     Pre => P'First <= I and then J <= P'Last + 1;
   function Eval_Polynomial (P : Polynomial) return Ring
   is (Eval_Polynomial_Range (P, P'First, P'Last + 1));

   function Evaluate_Polynomial_Effective (P : Polynomial) return Ring
     with Global => null,
     Post => Evaluate_Polynomial_Effective'Result = Eval_Polynomial (P);

   function Evaluate_Polynomial_Weakly_Effective (P : Polynomial) return Ring
     with Global => null,
     Post => Evaluate_Polynomial_Weakly_Effective'Result = Eval_Polynomial (P);

   function Evaluate_Polynomial_Ineffective (P : Polynomial) return Ring
     with Global => null,
     Post => Evaluate_Polynomial_Ineffective'Result = Eval_Polynomial (P); --@POSTCONDITION:FAIL

   procedure Add_Assoc (X, Y, Z : Ring)
     with Ghost,
     Global => null,
     Always_Terminates => True,
     Post => (X +Y) + Z = X + (Y + Z);

   procedure Mul_Assoc (X, Y, Z : Ring)
     with Ghost,
     Global => null,
     Always_Terminates => True,
     Post => (X * Y) * Z = X * (Y * Z);

   procedure Mul_One (X : ring)
     with Ghost,
     Global => null,
     Always_Terminates => True,
     Post => (X * 1) = X and (1 * X) = X;

   procedure Eval_Monomial_Catenation (M : Monomial; I, J, K : Integer)
     with Ghost,
     Global => null,
     Always_Terminates => True,
     Pre => M'First <= I and I <= J and J <= K and K <= M'Last + 1,
     Post => Eval_Monomial_Range (M, I, K)
       = Eval_Monomial_Range (M, I, J) * Eval_Monomial_Range (M, J, K),
     Subprogram_Variant => (Increases => I);

   procedure Mul_Assoc (X, Y, Z : Ring) is null;
   procedure Add_Assoc (X, Y, Z : Ring) is null;
   procedure Mul_One (X : Ring) is null;

   procedure Eval_Monomial_Catenation (M : Monomial; I, J, K : Integer) is
   begin
      if I /= J then
         Mul_Assoc (Eval_Var (M (I)),
                    Eval_Monomial_Range (M, I+1, J),
                    Eval_Monomial_Range (M, J, K));
         Eval_Monomial_Catenation (M, I+1, J, K);
      else
         Mul_One (Eval_Monomial_Range (M, J, K));
      end if;
   end Eval_Monomial_Catenation;

   function Evaluate_Polynomial_Effective (P : Polynomial) return Ring is
      Acc : Ring := 0;
   begin
      Outer: for I in P'Range loop
         pragma Loop_Invariant
           (Eval_Polynomial (P)
            = Acc + Eval_Polynomial_Range (P, I, P'Last + 1));
         declare
            Mul : Ring := P (I).Coeff;
            Mon : not null access constant Monomial := P(I).Mono;
         begin
            for J in Mon.all'Range loop
               pragma Loop_Invariant
                 (P(I).Coeff * Eval_Monomial (Mon.all)
                  = Mul * Eval_Monomial_Range (Mon.all, J, Mon.all'Last + 1));
               Mul_Assoc
                 (Mul,
                  Eval_Var (Mon.all (J)),
                  Eval_Monomial_Range (Mon.all, J+1, Mon.all'Last+1));
               Mul := Mul * Eval_Var (Mon.all (J));
               continue Outer when Mul = 0;
            end loop;
            Mul_One (Mul);
            pragma Assert (Mul = P (I).Coeff * Eval_Monomial (Mon.all));
            Add_Assoc (Acc, Mul, Eval_Polynomial_Range (P, I+1, P'Last+1));
            Acc := Acc + Mul;
         end;
      end loop Outer;
      return Acc;
   end Evaluate_Polynomial_Effective;

   function Evaluate_Polynomial_Weakly_Effective (P : Polynomial) return Ring is
      Acc : Ring := 0;
      function Skip_Less (X : Ring) return Boolean
        with Import, Global => null, Post => (if Skip_Less'Result then X = 0);
   begin
      Outer: for I in P'Range loop
         pragma Loop_Invariant
           (Eval_Polynomial (P)
            = Acc + Eval_Polynomial_Range (P, I, P'Last + 1));
         declare
            Mul : Ring := P (I).Coeff;
            Mon : not null access constant Monomial := P(I).Mono;
         begin
            for J in Mon.all'Range loop
               pragma Loop_Invariant
                 (P(I).Coeff * Eval_Monomial (Mon.all)
                  = Mul * Eval_Monomial_Range (Mon.all, J, Mon.all'Last + 1));
               Mul_Assoc
                 (Mul,
                  Eval_Var (Mon.all (J)),
                  Eval_Monomial_Range (Mon.all, J+1, Mon.all'Last+1));
               Mul := Mul * Eval_Var (Mon.all (J));
               continue Outer when Skip_Less (Mul);
            end loop;
            Mul_One (Mul);
            pragma Assert (Mul = P (I).Coeff * Eval_Monomial (Mon.all));
            Add_Assoc (Acc, Mul, Eval_Polynomial_Range (P, I+1, P'Last+1));
            Acc := Acc + Mul;
         end;
      end loop Outer;
      return Acc;
   end Evaluate_Polynomial_Weakly_Effective;

   function Evaluate_Polynomial_Ineffective (P : Polynomial) return Ring is
      Acc : Ring := 0;
      function Skip_More (X : Ring) return Boolean
        with Import, Global => null, Post => (if X = 0 then Skip_More'Result = True);
   begin
      Outer: for I in P'Range loop
         pragma Loop_Invariant (Eval_Polynomial (P) = Acc + Eval_Polynomial_Range (P, I, P'Last + 1)); --@LOOP_INVARIANT_PRESERV:FAIL
         declare
            Mul : Ring := P (I).Coeff;
            Mon : not null access constant Monomial := P(I).Mono;
         begin
            for J in Mon.all'Range loop
               pragma Loop_Invariant
                 (P(I).Coeff * Eval_Monomial (Mon.all)
                  = Mul * Eval_Monomial_Range (Mon.all, J, Mon.all'Last + 1));
               Mul_Assoc
                 (Mul,
                  Eval_Var (Mon.all (J)),
                  Eval_Monomial_Range (Mon.all, J+1, Mon.all'Last+1));
               Mul := Mul * Eval_Var (Mon.all (J));
               continue Outer when Skip_More (Mul);
            end loop;
            Mul_One (Mul);
            pragma Assert (Mul = P (I).Coeff * Eval_Monomial (Mon.all));
            Add_Assoc (Acc, Mul, Eval_Polynomial_Range (P, I+1, P'Last+1));
            Acc := Acc + Mul;
         end;
      end loop Outer;
      return Acc;
   end Evaluate_Polynomial_Ineffective;

begin
   null;
end Polynomial;
