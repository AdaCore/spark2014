package Substract is
   function Sub (First : Integer; Second : Integer) return Integer
      with Post => (Sub'Result = First - Second);

   function SubSimp (First : Integer; Second : Integer) return Integer
      with Post => (SubSimp'Result = First - Second);

   function OppSub (First : Integer; Second : Integer) return Integer
      with Post => (OppSub'Result = Second - First);

   function SubInv (First : Integer; Second : Integer) return Integer
      with Post => (SubInv'Result = First - Second);

   function Add3 (First : Integer; Second : Integer; Third : Integer)
      return Integer;
   function AddPart return Integer;
end Substract;
