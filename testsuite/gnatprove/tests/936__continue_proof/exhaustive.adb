pragma Extensions_Allowed (All_Extensions);
procedure Exhaustive with SPARK_Mode is
   function Property_P (X : Integer) return Boolean
     with Import, Global => null;
   function Property_Q (X : Integer) return Boolean
     with Import, Global => null;
   type Arr is array (Integer range <>) of Integer;
   function Test_Implication (A : Arr) return Boolean
     with Post => Test_Implication'Result = (for all X of A =>
                                               (if Property_P (X)
                                                    then Property_Q (X)));
   function Test_Implication (A : Arr) return Boolean is
   begin
      for I in A'Range loop
         pragma Loop_Invariant
           (if I > A'First then
              (for all J in A'First .. I - 1 =>
                   (if Property_P (A (J)) then Property_Q (A (J)))));
         continue when Property_Q (A (I));
         if Property_P (A (I)) then
            return False;
         end if;
      end loop;
      return True;
   end Test_Implication;

begin
   null;
end Exhaustive;
