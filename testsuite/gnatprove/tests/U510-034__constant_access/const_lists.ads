package Const_Lists with SPARK_Mode is
   type List;
   type List_Acc is access constant List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   X : constant List_Acc :=
     new List'(V => 1,
               N => new List'(V => 2,
                              N => new List'(V => 3,
                                             N => new List'(V => 4,
                                                            N => null))));

   V : constant List :=
     (V => 1,
      N => new List'(V => 2,
                     N => new List'(V => 3,
                                    N => new List'(V => 4,
                                                   N => null))));
   type List2;
   type List2_Acc is access constant List2;
   type Int_Acc is access Integer;
   type List2 is record
      V : Int_Acc;
      N : List2_Acc;
   end record;

   function New_Int (X : Integer) return Int_Acc is (new Integer'(X));

   Y : constant List2_Acc :=
     new List2'(V => new Integer'(1),
                N => new List2'(V => new Integer'(2),
                                N => new List2'(V => new Integer'(3),
                                                N => new List2'(V => new Integer'(4),
                                                                N => null))));
   Z : constant List2_Acc :=
     new List2'(V => New_Int (1),
                N => new List2'(V => New_Int (2),
                                N => new List2'(V => New_Int (3),
                                                N => new List2'(V => New_Int (4),
                                                                N => null))));
   type List3;
   type List3_Acc is access constant List3;
   type Cst_Int_Acc is access constant Integer;
   type List3 is record
      V : Cst_Int_Acc;
      N : List3_Acc;
   end record;

   U : constant List3_Acc :=
     new List3'(V => Cst_Int_Acc (New_Int (1)),
                N => new List3'(V => Cst_Int_Acc (New_Int (2)),
                                N => new List3'(V => Cst_Int_Acc (New_Int (3)),
                                                N => new List3'(V => Cst_Int_Acc (New_Int (4)),
                                                                N => null))));
   type List4;
   type List4_Acc is access List4;
   type List4 is record
      V : Cst_Int_Acc;
      N : List4_Acc;
   end record;
   type C_List4_Acc is access constant List4;
   type Holder is record
      Content : C_List4_Acc;
   end record;

   W : constant Holder :=
     (Content => C_List4_Acc
        (List4_Acc'(new List4'(V => Cst_Int_Acc (New_Int (1)),
                               N => new List4'(V => Cst_Int_Acc (New_Int (2)),
                                               N => new List4'(V => new Integer'(3),
                                                               N => new List4'(V => new Integer'(4),
                                                                               N => null)))))));
end Const_Lists;
