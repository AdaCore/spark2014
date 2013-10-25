package body Initial_Condition_Illegal
  with SPARK_Mode
is
   package body Incorrect_Placement
     with Refined_State     => (State => Flag),
          Initial_Condition => F1
   is
      Flag : Boolean := True;

      function F1 return Boolean is (Flag)
        with Refined_Global => Flag;
   end Incorrect_Placement;


   package body Incorrect_Order_1
     with Refined_State => (State => Flag)
   is
      Flag : Boolean := True;

      function F1 return Boolean is (Flag)
        with Refined_Global => Flag;
   end Incorrect_Order_1;


   package body Incorrect_Order_2
     with Refined_State => (State => Flag)
   is
      Flag : Boolean := True;

      function F1 return Boolean is (Flag)
        with Refined_Global => Flag;
   end Incorrect_Order_2;


   package body Variable_Not_Denoted_By_Initializes is
      procedure P1 is begin null; end P1;
   begin
      Var := 0;
   end Variable_Not_Denoted_By_Initializes;
end Initial_Condition_Illegal;
