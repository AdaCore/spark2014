procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;
   type T is record
      F, G : aliased Int_Acc;
   end record;
   type T_Acc is access T;
   function F (X : access T) return access Int_Acc is
   begin
      return X.F'Access;
   end F;
   X : Int_Acc;
   Z : T_Acc := new T'(new Integer'(1), new Integer'(2));
begin
    X := F (Z).all;
end;
