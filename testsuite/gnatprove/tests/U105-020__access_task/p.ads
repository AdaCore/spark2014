package P with SPARK_Mode is
   type Int_Ptr is access Boolean;
   X : constant Int_Ptr := new Boolean'(True);
   task type TT with Global => (In_Out => X);
end P;
