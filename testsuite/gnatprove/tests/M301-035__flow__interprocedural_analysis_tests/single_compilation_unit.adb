package body Single_Compilation_Unit is
   --  This package checks that the IFA produces correct
   --  CFGs and PDGs for subroutines that call other
   --  subroutines of the same compilation unit.

   Condition: Boolean;
   X, Y: Integer;

   --  Function Double_Max calls procedure Max.
   --  Since a contract has been supplied for
   --  Max, it will be used by Double_Max.

   function Double_Max return Integer;

   --  Procedure Max returns the maximum of two
   --  global parameters.

   procedure Max (Maximum: out Integer)
      with Global  => (X, Y),
           Depends => (Maximum => (X, Y));


   --  Procedures Mutual_Recursion_A and Mutual_Recursion_B
   --  call each other. Their respective PDGs contain each
   --  others's contracts.

   procedure Mutual_Recursion_A
      with Global  => (In_Out => (X, Y, Condition)),
           Depends => ((Condition, X, Y) =>+ Condition);

   procedure Mutual_Recursion_B
      with Global  => (In_Out => (X, Y, Condition)),
           Depends => ((Condition, X, Y) =>+ Condition);

   ----------------
   -- Double_Max --
   ----------------

   function Double_Max return Integer is
      Temp: Integer;
   begin
      Max (Temp);
      return 2 * Temp;
   end Double_Max;

   ---------------
   -- Factorial --
   ---------------

   procedure Factorial (Var: Natural; Fact: out Natural) is
   begin
      if Var > 1 then
         Factorial (Var - 1, Fact);
         Fact := Fact * Var;
      else
         Fact := 1;
      end if;
   end Factorial;

   ---------------
   -- Fibonacci --
   ---------------

   function Fibonacci (N: Integer) return Integer is
   begin
      if N < 3 then
         return 1;
      else
         return Fibonacci (N - 1) + Fibonacci (N - 2);
      end if;
   end Fibonacci;

   ---------
   -- Max --
   ---------

   procedure Max (Maximum: out Integer) is
   begin
      if X > Y then
         Maximum := X;
         return;
      end if;
      Maximum := Y;
   end Max;

   ------------------------
   -- Mutual_Recursion_A --
   ------------------------

   procedure Mutual_Recursion_A is
   begin
      if Condition then
         Condition := False;
         X := 2 * X;
      else
         Mutual_Recursion_B;
      end if;
   end;

   ------------------------
   -- Mutual_Recursion_B --
   ------------------------

   procedure Mutual_Recursion_B is
   begin
      if Condition then
         Condition := False;
         Y := 2 * Y;
      else
         Mutual_Recursion_A;
      end if;
   end;
end Single_Compilation_Unit;
