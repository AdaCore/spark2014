package P is
   protected type PT is
      function Id1 (X : Integer) return Integer with Depends => (Id1'Result => X, null => PT);
      function Id2 (X : Integer) return Integer with Depends => (Id2'Result => X, null => PT);
   end PT;
end P;
