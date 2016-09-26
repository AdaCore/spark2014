package P.Child is

   procedure Test_01;
   --  Unannotated

   procedure Test_02
   with Global => (Output => State);
   --  Only global

   procedure Test_03
   with Global => (Output => State);
   --  Global and refined_global

   procedure Test_04
   with Global => (Output => State);
   --  Using unannotated, with only global

   procedure Test_05
   with Global => (Output => State);
   --  Using unannotated, with global and refined_global

end P.Child;
