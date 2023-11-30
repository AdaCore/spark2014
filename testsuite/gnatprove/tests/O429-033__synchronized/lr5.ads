with YSO; use YSO;

package LR5 with SPARK_Mode is
   type Rec_1 is record
      Comp_1 : Integer := 1;
      Comp_2 : Prot_Typ;                                             --  Error
   end record with Volatile;

   type Rec_2 is record
      Comp_1 : Integer := 1;
      Comp_2 : Task_Typ;                                             --  Error
   end record with Volatile;

   type Rec_3 is record
      Comp_1 : Integer := 1;
      Comp_2 : Arr_Typ;                                              --  Error
   end record with Volatile;

   type Rec_4 is record
      Comp_1 : Integer := 1;
      Comp_2 : Sus_Obj;                                              --  Error
   end record with Volatile;

   type Rec_5 is record
      Comp_1 : Integer := 1;
      Comp_2 : Rec_Typ;                                              --  Error
   end record with Volatile;

   type Rec_6 is record
      Comp_1 : Integer := 1;
      Comp_2 : Deriv_Typ;                                            --  Error
   end record with Volatile;
end LR5;
