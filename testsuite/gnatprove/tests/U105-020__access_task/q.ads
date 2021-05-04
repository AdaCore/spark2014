package Q with SPARK_Mode is
   type Int_Ptr is access Boolean;
   X : constant Int_Ptr := new Boolean'(True);
   procedure Proc with Global => (In_Out => X);
end Q;
