package P is
   protected type PT is

      function Sum1 (Param : Integer) return Integer
      with Depends => (Sum1'Result => (Param), null => PT);

      function Sum2 (Param : Integer) return Integer
      with Depends => (Sum2'Result => (Param, PT));

      --  Those two functions have identical bodies, but different Depends
      --  contracts; I think at least one of this contracts must be wrong.

   private
      Protected_Data : Integer := 0;
   end;
end;
