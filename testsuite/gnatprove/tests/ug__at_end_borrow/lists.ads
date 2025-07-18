package Lists with SPARK_Mode is

   type List;
   type List_Acc is access List;
   type List is record
      Val  : Integer;
      Next : List_Acc;
   end record;

   function At_End_Borrow (L : access constant List) return access constant List is
     (L)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

end Lists;
