procedure Test_Nested_Calls with SPARK_Mode is
   function Identity (X : not null access constant Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      return X; -- @ACCESSIBILITY_CHECK:PASS
   end Identity;

   function Forward (X : not null access constant Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      return Identity (X); -- @ACCESSIBILITY_CHECK:PASS
   end Forward;

   function Nested (X : not null access constant Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      return Identity (Identity (X)); -- @ACCESSIBILITY_CHECK:FAIL
   end Nested;

   function Borrow (X : not null access Integer)
     return not null access Integer
     with Global => null
   is
   begin
      return X; -- @ACCESSIBILITY_CHECK:PASS
   end Borrow;

   function Nested_Borrow (X : not null access Integer)
     return not null access Integer
     with Global => null
   is
   begin
      return Borrow (Borrow (X)); -- @ACCESSIBILITY_CHECK:FAIL
   end Nested_Borrow;

   function Aliased_Identity (X : aliased Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      return X'Access;
   end Aliased_Identity;

   function Forward_Aliased (X : aliased Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      return Aliased_Identity (X); -- @ACCESSIBILITY_CHECK:PASS
   end Forward_Aliased;

   function Nested_Access (X : aliased Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      return Identity (Aliased_Identity (X)); -- @ACCESSIBILITY_CHECK:FAIL
   end Nested_Access;

   function Nested_Aliased (X : aliased Integer)
     return not null access constant Integer
     with Global => null
   is
   begin
      --  Keep this chain unproved pending clarification of its call masters
      return Aliased_Identity (Aliased_Identity (X).all); -- @ACCESSIBILITY_CHECK:FAIL
   end Nested_Aliased;
begin
   null;
end Test_Nested_Calls;
