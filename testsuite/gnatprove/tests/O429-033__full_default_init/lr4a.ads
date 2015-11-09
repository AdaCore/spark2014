package LR4a with SPARK_Mode is
   protected PT is
      entry Ent;
   end PT;

   task TT;

   type Rec_Typ is record
      Comp : Integer;
   end record;

   Var_1 : Natural with Part_Of => PT;                               --  Error
   Var_2 : Rec_Typ with Part_Of => TT;                               --  Error
   Var_3 : Natural;
   pragma Part_Of (PT);                                              --  Error
   Var_4 : Natural;
   pragma Part_Of (TT);                                              --  Error
end LR4a;
