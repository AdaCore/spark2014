package Count is
   function Count (Max : Integer; Step : Natural) return Natural
   with Pre =>
      (Step > 0 and then Max >= 0 and then Max < Integer'Last - Step),
     Post => Count'Result > Max and then Count'Result - Step <= Max;
end Count;
