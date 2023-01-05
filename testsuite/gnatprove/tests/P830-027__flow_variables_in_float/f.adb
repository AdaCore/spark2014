function F (X : Float; Y : Integer) return Boolean is

   subtype Float_Type is Float range 0.0 .. X;
   subtype Int_Type   is Integer range 0 .. Y;

begin
   return Float'(1.0) in Float_Type and 1 in Int_Type;
end;
