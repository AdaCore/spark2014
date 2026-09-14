procedure Main with SPARK_Mode is

   type Int_Or_Float (Is_Int : Boolean := True) is record
      case Is_Int is
      when True =>
         My_Int : Integer;
      when False =>
         My_Float : Integer;
      end case;
   end record with Unchecked_Union;

   procedure Increase_Int_Value
     (X : in out Int_Or_Float)
     with
       Pre  => (Static => X.Is_Int and then
                  X.My_Int < Integer'Last),
       Post => (Static => X.Is_Int and
                  X.My_Int = X.My_Int'Old + 1)
   is
   begin
      X.My_Int := X.My_Int + 1;
   end Increase_Int_Value;

begin
   null;
end Main;
