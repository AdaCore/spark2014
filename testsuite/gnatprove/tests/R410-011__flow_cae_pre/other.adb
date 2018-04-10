package body Other is
   X : Boolean := True with Constant_After_Elaboration;
   function Read_Hidden_CAE return Boolean is (X);
end;
