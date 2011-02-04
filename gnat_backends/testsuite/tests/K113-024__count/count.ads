package Count is
   function Count (Max : Integer; Step : Integer) return Integer
   with Pre => Step > 0 and Max >= 0,
     Post => Count'Result > Max and Count'Result <= Max + Step;
end Count;
