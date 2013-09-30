package Ghost_Legal
  with SPARK_Mode
is
   function Is_Even (X : Natural) return Boolean
     with Convention => Ghost;

   function Is_Prime (X : Natural) return Boolean
     with Post => (if Is_Even (X) then not Is_Prime'Result);
end Ghost_Legal;
