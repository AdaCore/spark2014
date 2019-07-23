with New_Eq; use New_Eq;
procedure Use_My_eq with SPARK_Mode is
   type Holder is record
      Content : New_Eq.T;
   end record;
   X, Y  : Holder;
begin
   pragma Assume (X = Y);
   pragma Assert (My_prop (X.Content, Y.Content));
end Use_My_eq;
