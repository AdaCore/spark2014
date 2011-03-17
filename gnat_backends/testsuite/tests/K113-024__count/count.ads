package Count is
   function Count (Max : Integer; Step : Natural) return Natural
   with Pre =>
      (Step > 0 and Max >= 0 and Max < Integer'Last - Step),
     Post => Count'Result > Max and Count'Result <= Max + Step;
end Count;
