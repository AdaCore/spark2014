procedure Test with SPARK_Mode is
   type Int_Acc is access Integer;
   function At_End (X : access constant Integer) return access constant Integer
   is (X)
     with Ghost, Annotate => (GNATprove, At_End_Borrow);

   function Stupid (X : Int_Acc) return access Integer;

   function Stupid (X : Int_Acc) return access Integer is (null);

   function Stupid_2 (X : Int_Acc) return access Integer with
     Post => At_End (Stupid_2'Result) = null
     and (At_End (X) = null) = (X = null)
     and (if X /= null then At_End (X).all = X.all);

   function Stupid_2 (X : Int_Acc) return access Integer is
   begin
      return null;
   end Stupid_2;

   X : Int_Acc := new Integer'(23);
begin
   declare
      B : access Integer := Stupid (X);
   begin
      pragma Assert (B = null);
      pragma Assert (At_End (B) = null);
      pragma Assert (At_End (X) /= null);
   end;
   pragma Assert (X.all = 23);
end Test;
