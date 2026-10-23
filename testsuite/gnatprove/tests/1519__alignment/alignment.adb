procedure Alignment (Result : out Boolean) with SPARK_Mode is
   type Rec is record
      I : Integer;
      B : Boolean;
   end record;
begin
   --  Exercise implicit alignment without native data representation information
   Result := Rec'Alignment = Rec'Alignment;
   pragma Assert (Result);
end Alignment;
